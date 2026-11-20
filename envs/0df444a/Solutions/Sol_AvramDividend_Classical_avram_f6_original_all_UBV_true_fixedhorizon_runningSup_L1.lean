-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_all_UBV_true_fixedhorizon_runningSup_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T19:36:13.528002+00:00
-- url     : https://prove2.me/submissions/c9d64d27-df79-4d4b-8eda-37302a6ac0bf

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_positive_esscher_root_of_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_avram_f6_original_positive_psi_root_runningSup_exp_L1
import Theorems.Thm_AvramDividend_Classical_levy_runningSup_joint_time_path_measurable
import Theorems.Thm_AvramDividend_Classical_runningSup_eq_rawSup_nonneg
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (n : ℝ≥0) :
    Integrable (fun ω : Ω => runningSup X n ω) P := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨lam, hlam, hroot⟩ :=
    positive_esscher_root_of_unbounded_variation X hBV 1 (by norm_num)
  let β : ℝ := lam / 2
  have hβpos : 0 < β := by dsimp [β]; linarith
  have hβlt : β < lam := by dsimp [β]; linarith
  have hExp : Integrable
      (fun ω : Ω => Real.exp (β * runningSup X n ω)) P :=
    avram_f6_original_positive_psi_root_runningSup_exp_L1
      X 1 lam β (by norm_num) hlam hroot hβpos.le hβlt n
  have hScaled := hExp.const_mul β⁻¹
  have hMeas : AEStronglyMeasurable (fun ω : Ω => runningSup X n ω) P := by
    have ht : Measurable (fun ω : Ω => (n, ω)) := by fun_prop
    exact ((levy_runningSup_joint_time_path_measurable X).comp ht).aestronglyMeasurable
  apply hScaled.mono' hMeas
  apply Filter.Eventually.of_forall
  intro ω
  have hz : 0 ≤ runningSup X n ω :=
    (runningSup_eq_rawSup_nonneg X n ω).2
  have he : β * runningSup X n ω ≤
      Real.exp (β * runningSup X n ω) := by
    have h := Real.add_one_le_exp (β * runningSup X n ω)
    linarith
  change |runningSup X n ω| ≤
    β⁻¹ * Real.exp (β * runningSup X n ω)
  rw [abs_of_nonneg hz]
  calc
    runningSup X n ω = β⁻¹ * (β * runningSup X n ω) := by
      field_simp
    _ ≤ β⁻¹ * Real.exp (β * runningSup X n ω) :=
      mul_le_mul_of_nonneg_left he (inv_nonneg.mpr hβpos.le)
