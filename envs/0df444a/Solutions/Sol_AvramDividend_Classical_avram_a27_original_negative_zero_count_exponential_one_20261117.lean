-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_negative_zero_count_exponential_one_20261117
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T16:08:19.087335+00:00
-- url     : https://prove2.me/submissions/3b9230e3-581c-4b04-8c7d-d55333365059

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

/-- The physical negative-jump exponential is one on an empty original jump-count cell. -/
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
    ∀ᵐ ω ∂P, K ω = 0 → Real.exp (θ * J ω) = 1 := by
  classical
  have hSupport :=
    avram_a26_original_physical_Borel_count_exact_finite_marked_support_20261116
      X hFinite t (Iio (0 : ℝ)) measurableSet_Iio (Subset.rfl) K hK hCount
  have hProduct :=
    avram_a88_original_physical_negative_jump_exponential_finite_product_20261114
      X hFinite t θ J hJEq
  filter_upwards [hSupport, hProduct] with ω hS hU hZero
  rcases hS with ⟨S, hSSpec, hCard⟩
  rcases hU with ⟨U, hUSpec, hProd⟩
  have hEmptyS : S = ∅ := Finset.card_eq_zero.mp (by
    rw [← hCard]
    exact hZero)
  have hUS : U = S := by
    ext u
    rw [hUSpec, hSSpec]
    constructor
    · rintro ⟨hpos, htime, hnonzero⟩
      have hnonpos := avram_wave4_04a_actual_levy_jumpmark_nonpositive
        X ω u hpos
      exact ⟨hpos, htime, hnonzero,
        lt_of_le_of_ne hnonpos hnonzero⟩
    · rintro ⟨hpos, htime, hnonzero, _⟩
      exact ⟨hpos, htime, hnonzero⟩
  have hEmptyU : U = ∅ := hUS.trans hEmptyS
  simpa [hEmptyU] using hProd
