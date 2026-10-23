-- Prove2me | solution 1 for AvramDividend.Classical.causal_l1_kernel_locally_bounded_input_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T22:33:56.461834+00:00
-- url     : https://prove2.me/submissions/ed3eacc6-d4af-477a-9d44-821d1c6ddc78

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_causal_l1_kernel_continuous_input_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (K V : ℝ → ℝ)
    (hK : IntegrableOn K (Ioi (0 : ℝ)) volume)
    (hVc : ContinuousOn V (Ioi (0 : ℝ)))
    (hVb : ∀ R : ℝ, 0 < R →
      ∃ C : ℝ, ∀ s : ℝ, s ∈ Ioc (0 : ℝ) R → |V s| ≤ C)
    (x : ℝ) (hx : 0 < x) :
    IntegrableOn (fun s : ℝ => K (x - s) * V s)
      (Ioc (0 : ℝ) x) volume := by
  have hKshift : IntegrableOn (fun s : ℝ => K (x - s))
      (Ioc (0 : ℝ) x) volume := by
    have hunit := causal_l1_kernel_continuous_input_integrable
      K (fun _ : ℝ => (1 : ℝ)) hK continuousOn_const x hx
    simpa only [mul_one] using hunit
  have hVcont : ContinuousOn V (Ioc (0 : ℝ) x) :=
    hVc.mono (by intro s hs; exact hs.1)
  have hVmeas : AEStronglyMeasurable V
      (volume.restrict (Ioc (0 : ℝ) x)) :=
    hVcont.aestronglyMeasurable measurableSet_Ioc
  obtain ⟨C, hC⟩ := hVb x hx
  have hVbound : ∀ᵐ s ∂volume.restrict (Ioc (0 : ℝ) x),
      ‖V s‖ ≤ |C| := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact le_trans (by simpa only [Real.norm_eq_abs] using hC s hs)
      (le_abs_self C)
  have hIntegrable := hKshift.bdd_mul hVmeas hVbound
  change Integrable (fun s : ℝ => K (x - s) * V s)
      (volume.restrict (Ioc (0 : ℝ) x))
  simpa only [mul_comm] using hIntegrable
