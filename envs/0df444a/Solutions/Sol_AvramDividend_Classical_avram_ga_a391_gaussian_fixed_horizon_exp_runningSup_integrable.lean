-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a391_gaussian_fixed_horizon_exp_runningSup_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:36:15.094439+00:00
-- url     : https://prove2.me/submissions/ce41c702-f768-49a5-8843-63dbdfdfe6be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_ga_a40_original_gaussian_fixed_horizon_exponential_integrable
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hSigma : 0 < X.σ)
    (n : ℝ≥0) (β : ℝ) (hβ : 0 ≤ β) :
    Integrable (fun ω : Ω => Real.exp (β * runningSup X n ω)) P := by
  have hn : Measurable (fun _ : Ω => (n : ℝ≥0)) := measurable_const
  have hId : Measurable (fun ω : Ω => ω) := measurable_id
  have hPair : Measurable (fun ω : Ω => ((n : ℝ≥0), ω)) :=
    hn.prod hId
  have hSup : Measurable (fun ω : Ω => runningSup X n ω) :=
    (levy_runningSup_joint_time_path_measurable X).comp hPair
  have hMeas : Measurable (fun ω : Ω =>
      Real.exp (β * runningSup X n ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hSup)
  refine ⟨hMeas.aestronglyMeasurable, ?_⟩
  have hMoment := avram_ga_a40_original_gaussian_fixed_horizon_exponential_integrable
    X hSigma n β hβ
  have hNorm (ω : Ω) :
      ‖Real.exp (β * runningSup X n ω)‖ₑ =
      ENNReal.ofReal (Real.exp (β * runningSup X n ω)) := by
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  change (∫⁻ ω : Ω, ‖Real.exp (β * runningSup X n ω)‖ₑ ∂P) < ⊤
  simp_rw [hNorm]
  exact hMoment
