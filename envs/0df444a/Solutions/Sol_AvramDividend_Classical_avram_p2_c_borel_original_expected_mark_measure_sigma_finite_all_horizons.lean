-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_original_expected_mark_measure_sigma_finite_all_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:08:06.140663+00:00
-- url     : https://prove2.me/submissions/bb35701c-e32a-473d-b509-f1b9a7203934

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_additive_mean_measure_negative_support
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_original_separated_band_finite_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_sigma_finite_of_negative_tail_cover
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual original source expected mark measure is sigma finite at
every elapsed-time horizon, including the empty zero horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕) :
    ∃ μ : ℝ≥0 → Measure ℝ,
      (∀ (T : ℝ≥0) (B : Set ℝ), MeasurableSet B →
        μ T B =
          (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            (Ioc 0 T ×ˢ B) ∂P)) ∧
      (∀ T : ℝ≥0, SigmaFinite (μ T)) := by
  obtain ⟨μ, hRep, _, _, hSupp⟩ :=
    avram_p2_c_borel_original_additive_mean_measure_negative_support X
  refine ⟨μ, hRep, ?_⟩
  intro T
  have hempty : Ici (0 : ℝ) ∩ Iio (0 : ℝ) = ∅ := by
    ext x
    constructor
    · rintro ⟨hxge, hxlt⟩
      change (0 : ℝ) ≤ x at hxge
      change x < (0 : ℝ) at hxlt
      linarith
    · intro hx
      exact hx.elim
  have hZero : μ T (Ici (0 : ℝ)) = 0 := by
    rw [hSupp T (Ici (0 : ℝ)) measurableSet_Ici, hempty, measure_empty]
  have hTail : ∀ ε : ℝ, 0 < ε → μ T (Iic (-ε)) < ⊤ := by
    intro ε hε
    by_cases hT : T = 0
    · subst T
      rw [hRep 0 (Iic (-ε)) measurableSet_Iic]
      simp
    · have hTpos : (0 : ℝ≥0) < T := pos_iff_ne_zero.mpr hT
      rw [hRep T (Iic (-ε)) measurableSet_Iic]
      exact avram_p2_c_borel_original_separated_band_finite_mean X T hTpos ε hε
  exact avram_p2_c_borel_sigma_finite_of_negative_tail_cover (μ T) hZero hTail
