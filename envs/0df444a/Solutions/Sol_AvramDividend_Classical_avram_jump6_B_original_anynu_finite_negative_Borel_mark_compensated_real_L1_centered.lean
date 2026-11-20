-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_anynu_finite_negative_Borel_mark_compensated_real_L1_centered
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T10:07:00.049611+00:00
-- url     : https://prove2.me/submissions/1ef0792b-3c16-4b68-89f5-86a9c3399c1a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_nu_centered_jump_mean_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hν : X.ν B < ⊤)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    Integrable (fun ω => (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) P ∧
      (∫ ω, (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal - (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∂P) = 0 := by
  have hRate :=
    avram_b24_original_negative_Borel_marked_Poisson_interval_Campbell_exact
      X s t hst B hB hNeg
  exact avram_p2_e_compensator_finite_nu_centered_jump_mean_zero
    X s t hst B hB hν hRate
