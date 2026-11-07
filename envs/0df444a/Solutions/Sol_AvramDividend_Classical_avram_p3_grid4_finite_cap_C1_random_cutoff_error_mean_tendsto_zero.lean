-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_random_cutoff_error_mean_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:04:56.361232+00:00
-- url     : https://prove2.me/submissions/3e64ddb1-b625-4f70-8540-dc73e67227ad

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under the original finite-cap BV C¹ secant hypotheses, random cap-corner errors
have expectations tending to zero on every probability space, provided each
actual source error is integrable. The cutoff bound is uniform in the path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (b : ℕ → ℝ) (hb0 : ∀ n, 0 ≤ b n)
    (hbC : ∀ n, b n ≤ C.toReal)
    (hb : Tendsto b atTop (𝓝 C.toReal))
    (Y : ℕ → Ω → ℝ) (hY : ∀ n, 0 ≤ᵐ[P] Y n)
    (hInt : ∀ n, Integrable (fun ω =>
      (if Y n ω ≤ C.toReal then w (Y n ω)
       else w C.toReal + (Y n ω - C.toReal)) -
      (if Y n ω ≤ b n then w (Y n ω)
       else w (b n) + (Y n ω - b n))) P) :
    Tendsto (fun n => ∫ ω,
      (if Y n ω ≤ C.toReal then w (Y n ω)
       else w C.toReal + (Y n ω - C.toReal)) -
      (if Y n ω ≤ b n then w (Y n ω)
       else w (b n) + (Y n ω - b n)) ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  let Err : ℕ → Ω → ℝ := fun n ω =>
    (if Y n ω ≤ C.toReal then w (Y n ω)
     else w C.toReal + (Y n ω - C.toReal)) -
    (if Y n ω ≤ b n then w (Y n ω)
     else w (b n) + (Y n ω - b n))
  have hcReal : 0 < C.toReal :=
    ENNReal.toReal_pos (ne_of_gt hC) hfinite
  have hDef :=
    avram_p3_grid4_finite_cap_corner_scalar_defect_tendsto_zero
      w C.toReal hcReal hw_cont b hb
  have hLow : ∀ n, 0 ≤ ∫ ω, Err n ω ∂P := by
    intro n
    apply integral_nonneg_of_ae
    filter_upwards [hY n] with ω hy
    exact (avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
      C hC hfinite w hw_cont hw_smooth hw_grad
      (b n) (Y n ω) (hb0 n) (hbC n) hy).1
  have hHi : ∀ n, (∫ ω, Err n ω ∂P) ≤
      (w C.toReal - w (b n)) - (C.toReal - b n) := by
    intro n
    have hAE : ∀ᵐ ω ∂P,
        Err n ω ≤ (w C.toReal - w (b n)) - (C.toReal - b n) := by
      filter_upwards [hY n] with ω hy
      exact (avram_p3_grid4_finite_cap_C1_uniform_cutoff_defect_bound
        C hC hfinite w hw_cont hw_smooth hw_grad
        (b n) (Y n ω) (hb0 n) (hbC n) hy).2
    have hM := integral_mono_ae (hInt n)
      (integrable_const ((w C.toReal - w (b n)) - (C.toReal - b n))) hAE
    simpa using hM
  exact squeeze_zero hLow hHi hDef
