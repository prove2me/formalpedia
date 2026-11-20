-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_positive_psi_root_runningSup_exp_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:29:21.127167+00:00
-- url     : https://prove2.me/submissions/463f0d5d-aaa9-45fb-9658-87861ec33d53

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_psi_root_true_fixedhorizon_expsup
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (p lam β : ℝ) (hp : 0 < p) (hlam : 0 < lam)
    (hroot : X.ψ lam = p) (hβ : 0 ≤ β) (hβlam : β < lam)
    (n : ℝ≥0) :
    Integrable (fun ω : Ω => Real.exp (β * runningSup X n ω)) P := by
  have hn : Measurable (fun _ : Ω => (n : ℝ≥0)) := measurable_const
  have hi : Measurable (fun ω : Ω => ω) := measurable_id
  have hPair : Measurable (fun ω : Ω => ((n : ℝ≥0), ω)) := hn.prod hi
  have hSup : Measurable (fun ω : Ω => runningSup X n ω) :=
    (levy_runningSup_joint_time_path_measurable X).comp hPair
  have hMeas : Measurable (fun ω : Ω =>
      Real.exp (β * runningSup X n ω)) :=
    Real.measurable_exp.comp (measurable_const.mul hSup)
  refine ⟨hMeas.aestronglyMeasurable, ?_⟩
  have hMoment :=
    avram_f6_original_positive_psi_root_true_fixedhorizon_expsup
      X p lam β hp hlam hroot hβ hβlam n
  have hNorm (ω : Ω) :
      ‖Real.exp (β * runningSup X n ω)‖ₑ =
      ENNReal.ofReal (Real.exp (β * runningSup X n ω)) := by
    rw [← ofReal_norm, Real.norm_eq_abs,
      abs_of_pos (Real.exp_pos _)]
  change (∫⁻ ω : Ω, ‖Real.exp (β * runningSup X n ω)‖ₑ ∂P) < ⊤
  simp_rw [hNorm]
  exact hMoment
