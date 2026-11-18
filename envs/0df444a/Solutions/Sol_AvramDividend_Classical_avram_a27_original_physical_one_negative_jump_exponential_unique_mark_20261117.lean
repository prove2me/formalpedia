-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_physical_one_negative_jump_exponential_unique_mark_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:44:12.944019+00:00
-- url     : https://prove2.me/submissions/a0bc8ea9-efc8-4aba-b8c1-a5223f1d6574

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
import Theorems.Thm_AvramDividend_Classical_avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_nonpositive
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- One actual negative physical jump makes the exponential weight its unique marked factor. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (J : Ω → ℝ)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun z : ℝ≥0 => X.X z ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (hCount : ∀ᵐ ω ∂P, (K ω : ℝ) =
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 t ×ˢ Iio (0 : ℝ))).toReal) :
    ∀ᵐ ω ∂P, K ω = 1 →
      ∃ u : ℝ≥0, 0 < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0 ∧
        Real.exp (θ * J ω) =
          Real.exp (θ * (X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
  classical
  have hSupport :=
    avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
      X hFinite t (Iio (0 : ℝ)) measurableSet_Iio (Subset.rfl) K hK hCount
  have hProduct :=
    avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
      X hFinite t θ J hJEq
  filter_upwards [hSupport, hProduct] with ω hS hU hk
  rcases hS with ⟨S, hSSpec, hCard⟩
  rcases hU with ⟨U, hUSpec, hProd⟩
  have hSingle : S.card = 1 := by
    rw [← hCard]
    exact hk
  rcases Finset.card_eq_one.mp hSingle with ⟨u, hu⟩
  have hUS : U = S := by
    ext v
    rw [hUSpec, hSSpec]
    constructor
    · rintro ⟨hpos, htime, hnonzero⟩
      have hnonpos := avram_wave4_04a_actual_levy_jumpmark_nonpositive
        X ω v hpos
      exact ⟨hpos, htime, hnonzero,
        lt_of_le_of_ne hnonpos hnonzero⟩
    · rintro ⟨hpos, htime, hnonzero, _⟩
      exact ⟨hpos, htime, hnonzero⟩
  have huS : u ∈ S := by simp [hu]
  obtain ⟨hPos, hTime, hNZ, hNeg⟩ := (hSSpec u).mp huS
  refine ⟨u, hPos, hTime, hNZ, ?_⟩
  simpa [hUS, hu, hTime] using hProd
