-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_mixed12_original_finite_activity_negative_count_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T14:43:10.68186+00:00
-- url     : https://prove2.me/submissions/baa32a2e-befc-44a7-8dc3-9bed8d0b697d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_negative_borel_mark_unconditional_levy_rate
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Finite Lévy mass gives almost-surely finite intrinsic negative-jump
counts on every bounded interval, including the Gaussian UBV branch. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) < ⊤ := by
  classical
  let N : Ω → ℝ≥0∞ := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ))
  have hMeas : Measurable N := by
    simpa only [N] using
      (avram_p2_e_compensator_original_intrinsic_marked_count_measurable
        X s t hst (Iio (0 : ℝ)) measurableSet_Iio)
  have hRate : (∫⁻ ω, N ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
    simpa only [N] using
      (avram_wave7_01_original_intrinsic_negative_borel_mark_unconditional_levy_rate
        X s t hst (Iio (0 : ℝ)) measurableSet_Iio (Subset.rfl))
  have hFin : (∫⁻ ω, N ω ∂P) ≠ ⊤ := by
    rw [hRate]
    exact ENNReal.mul_ne_top (by simp) hFinite
  simpa only [N] using (MeasureTheory.ae_lt_top hMeas hFin)
