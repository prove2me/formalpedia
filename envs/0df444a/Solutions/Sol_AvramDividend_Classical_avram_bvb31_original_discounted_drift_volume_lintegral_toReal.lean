-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb31_original_discounted_drift_volume_lintegral_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T17:11:14.8282+00:00
-- url     : https://prove2.me/submissions/9b65d20a-60bc-42f5-8bcf-fd2b1bcfd5a6

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bvb23_original_discounted_zero_contact_budget_identity
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set intervalIntegral AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
theorem solution
    (d q T : ℝ) (hd : 0 ≤ d) (hq : 0 < q) (hT : 0 ≤ T) :
    (∫⁻ t in Ioc (0 : ℝ) T,
      ENNReal.ofReal (Real.exp ((-q) * t))
        ∂((ENNReal.ofReal d) • (volume : Measure ℝ))).toReal =
      d * (∫ t in (0 : ℝ)..T, Real.exp ((-q) * t)) := by
  let f : ℝ → ℝ := fun t => Real.exp ((-q) * t)
  let I : ℝ := ∫ t in (0 : ℝ)..T, f t
  have hfCont : Continuous f :=
    Real.continuous_exp.comp (continuous_const.mul continuous_id)
  have hfInt : IntervalIntegrable f volume 0 T :=
    hfCont.intervalIntegrable _ _
  have hfLoc : IntegrableOn f (Ioc (0 : ℝ) T) volume :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hT).mp hfInt
  have hfPos : 0 ≤ᵐ[(volume : Measure ℝ).restrict (Ioc (0 : ℝ) T)] f :=
    Filter.Eventually.of_forall (fun _ => Real.exp_nonneg _)
  have hLin :
      (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (f t) ∂volume) =
        ENNReal.ofReal I := by
    have h := ofReal_integral_eq_lintegral_ofReal hfLoc hfPos
    rw [← intervalIntegral.integral_of_le hT] at h
    exact h.symm
  have hId :
      q * I + Real.exp ((-q) * T) = 1 := by
    exact avram_bvb23_original_discounted_zero_contact_budget_identity
      q T hq hT
  have hExp : Real.exp ((-q) * T) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [mul_nonneg hq.le hT])
  have hINonneg : 0 ≤ I := by
    dsimp [I, f] at hId ⊢
    nlinarith [hId]
  have hCash :
      (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (f t)
        ∂((ENNReal.ofReal d) • (volume : Measure ℝ))) =
      ENNReal.ofReal (d * I) := by
    rw [Measure.restrict_smul, lintegral_smul_measure, hLin]
    exact (ENNReal.ofReal_mul hd).symm
  change (∫⁻ t in Ioc (0 : ℝ) T, ENNReal.ofReal (f t)
        ∂((ENNReal.ofReal d) • (volume : Measure ℝ))).toReal = d * I
  rw [hCash, ENNReal.toReal_ofReal (mul_nonneg hd hINonneg)]
