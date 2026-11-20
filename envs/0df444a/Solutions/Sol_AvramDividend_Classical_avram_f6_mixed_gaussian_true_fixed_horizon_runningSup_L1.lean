-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_mixed_gaussian_true_fixed_horizon_runningSup_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:46:42.917949+00:00
-- url     : https://prove2.me/submissions/e1894885-ea92-403c-97f6-3c0a2a8dae01

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hSigma : 0 < X.σ)
    (n : ℝ≥0) :
    Integrable (fun ω : Ω => runningSup X n ω) P := by
  have hExp : Integrable
      (fun ω : Ω => Real.exp (runningSup X n ω)) P := by
    simpa using
      (avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable
        X hSigma n 1 (by norm_num))
  have hm : AEStronglyMeasurable
      (fun ω : Ω => runningSup X n ω) P := by
    have ht : Measurable (fun ω : Ω => (n, ω)) := by fun_prop
    have h := (levy_runningSup_joint_time_path_measurable X).comp ht
    exact h.aestronglyMeasurable
  apply hExp.mono' hm
  apply Filter.Eventually.of_forall
  intro ω
  have hnn : 0 ≤ runningSup X n ω :=
    (runningSup_eq_rawSup_nonneg X n ω).2
  change |runningSup X n ω| ≤ Real.exp (runningSup X n ω)
  rw [abs_of_nonneg hnn]
  have hexp := Real.add_one_le_exp (runningSup X n ω)
  linarith
