-- Prove2me | solution 1 for BianchiIX.exists_coreReflection_paid_step
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:08:29.748983+00:00
-- url     : https://prove2.me/submissions/399ea214-eb6c-41b1-8b4b-c3c20ab1419e

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_ProjectiveReflection
import Definitions.Def_BianchiIX_Dynamics_CoreEntryDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreReturnDifferential
import Definitions.Def_BianchiIX_Dynamics_CompactCoreReturn
import Definitions.Def_BianchiIX_EraReturnData
import Theorems.Thm_BianchiIX_exists_coreReflection_step
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Tactic.Module
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.SpecialFunctions.Pow.Real

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX

private theorem BianchiIX.affine_mul_exp_neg_le_one (x : ℝ) : (1 + x) * Real.exp (-x) ≤ 1 := by
  have H := mul_le_mul_of_nonneg_right (Real.add_one_le_exp x) (Real.exp_pos (-x)).le
  rw [← Real.exp_add, add_neg_cancel, Real.exp_zero] at H
  simpa only [add_comm] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.rpow_div_le_core_loss {a b k c p : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hk : 2 ≤ k) (hc : 0 < c) (hp : 0 < p) (hdec : b ≤ Real.exp (-c / k) * a) :
    a ^ p / k ≤ (1 + p * c / 2) / (p * c) * (a ^ p - b ^ p) := by
  have hk0 : 0 < k := by linarith only [hk]
  have hpc : 0 < p * c := mul_pos hp hc
  have hz : 0 ≤ p * c / k := (div_pos hpc hk0).le
  have hpow : b ^ p ≤ Real.exp (-(p * c / k)) * a ^ p := by
    have H := Real.rpow_le_rpow hb hdec hp.le
    rw [Real.mul_rpow (Real.exp_pos _).le ha, ← Real.exp_mul] at H
    convert! H using 1
    congr 2
    ring
  have hab : b ^ p ≤ a ^ p := hpow.trans
    ((mul_le_mul_of_nonneg_right (Real.exp_le_one_iff.mpr (neg_nonpos.mpr hz))
      (Real.rpow_nonneg ha p)).trans_eq (one_mul _))
  have H := mul_le_mul_of_nonneg_left hpow (by positivity : 0 ≤ 1 + p * c / k)
  have He := mul_le_mul_of_nonneg_right (affine_mul_exp_neg_le_one (p * c / k))
    (Real.rpow_nonneg ha p)
  have hpaid : (p * c / k) * a ^ p ≤ (1 + p * c / k) * (a ^ p - b ^ p) := by
    nlinarith only [H, He]
  have hzmax : p * c / k ≤ p * c / 2 :=
    div_le_div_of_nonneg_left hpc.le (by norm_num) hk
  have Hmax := mul_le_mul_of_nonneg_right (add_le_add_left hzmax 1) (sub_nonneg.mpr hab)
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ hpc).mpr
  calc
    a ^ p / k * (p * c) = (p * c / k) * a ^ p := by ring
    _ ≤ (1 + p * c / k) * (a ^ p - b ^ p) := hpaid
    _ ≤ (1 + p * c / 2) * (a ^ p - b ^ p) := by simpa only [add_comm] using Hmax

end
end


/-- On the full range above `4 - 1/16`, each actual step pays its phase error by wall loss. -/
theorem solution :
    ∃ δ > (0 : ℝ), δ ≤ 1 / 10000 ∧ ∃ C ≥ (1 : ℝ), ∀ Y : CoreAngleState,
      63 / 16 ≤ Y 0 → 0 < Y 1 → 0 < Y 2 → Y 1 + Y 2 ≤ δ / (1 + Y 0) →
      let G := coreReflectionState coreRadiusReturnTime
      coreRadiusReturnValid Y ∧ 0 < coreReflectionTime Y ∧
        coreRadiusEntry (G Y) = projectiveReflection
          (projectiveOriginalFlow (coreRadiusEntry Y) 0 (coreReflectionTime Y)) ∧
        (3 / 2 ≤ Y 0 - G Y 0 ∧ Y 0 - G Y 0 ≤ 5 / 2) ∧
        (∀ i : Fin 2, 0 < G Y i.succ ∧ G Y i.succ ≤ Y i.succ) ∧
        |G Y 0 - (Y 0 - 2)| ≤ C * ((Y 1 + Y 2) - (G Y 1 + G Y 2)) := by
  obtain ⟨ε, hε, hεmax, K, hK, c, hc, _, H⟩ := exists_coreReflection_step
  let δ := min ε (1 / (16 * K))
  let A := (1 + c / 2) / c
  have hδ : 0 < δ := lt_min hε (by positivity)
  have hA : 0 < A := by dsimp [A]; positivity
  refine ⟨δ, hδ, (min_le_left _ _).trans hεmax, max 1 (K * A), le_max_left _ _, ?_⟩
  intro Y hk hu hw hb G
  have hk2 : 2 ≤ Y 0 := by linarith only [hk]
  have hk0 : 0 < Y 0 := by linarith only [hk]
  have hb0 : 0 < Y 1 + Y 2 := add_pos hu hw
  have hbudget : δ / (1 + Y 0) ≤ ε / Y 0 :=
    (div_le_div_of_nonneg_left hδ.le hk0 (by linarith)).trans
      (div_le_div_of_nonneg_right (min_le_left _ _) hk0.le)
  have hsmall : Y 1 + Y 2 ≤ δ := hb.trans (div_le_self hδ.le (by linarith only [hk]))
  have hδK : K * δ ≤ 1 / 16 := by
    have HH := (le_div_iff₀ (mul_pos (by norm_num : (0 : ℝ) < 16) hK)).mp (min_le_right ε (1 / (16 * K)))
    nlinarith only [HH]
  obtain ⟨hvalid, _, _, hcore, hstep⟩ := H Y hk2
    ⟨hu, (by linarith only [hw, hb] : Y 1 ≤ δ / (1 + Y 0)).trans hbudget⟩
    ⟨hw, (by linarith only [hu, hb] : Y 2 ≤ δ / (1 + Y 0)).trans hbudget⟩
  let Z := coreReturnState coreRadiusReturnTime Y
  have herror : |Z 0 - Y 0| ≤ 1 / 16 := hcore.2.1.trans (by
    calc
      _ ≤ K * δ / Y 0 := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hsmall hK.le) hk0.le
      _ ≤ K * δ := div_le_self (mul_nonneg hK.le hδ.le) (by linarith only [hk])
      _ ≤ _ := hδK)
  have hguard : 31 / 8 ≤ Z 0 := by linarith only [hk, (abs_le.mp herror).1]
  obtain ⟨hT, horbit, _, _, _, herr, hdrop, hwall, _, _⟩ := hstep hguard
  have hnext (i : Fin 2) : 0 < G Y i.succ ∧ G Y i.succ ≤ Y i.succ := by
    refine ⟨(hwall i).2.1, (hwall i).2.2.1.trans ?_⟩
    have hpos : 0 ≤ Y i.succ := by
      fin_cases i
      · exact hu.le
      · exact hw.le
    exact (hwall i).2.2.2.trans ((mul_le_mul_of_nonneg_right
      (Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hc.le) hk0.le)) hpos).trans_eq (one_mul _))
  have hdec : Z 1 + Z 2 ≤ Real.exp (-c / Y 0) * (Y 1 + Y 2) := by
    simpa only [Z, mul_add] using! add_le_add (hwall 0).2.2.2 (hwall 1).2.2.2
  have hconn : G Y 1 + G Y 2 ≤ Z 1 + Z 2 := add_le_add (hwall 0).2.2.1 (hwall 1).2.2.1
  have hpaid : (Y 1 + Y 2) / Y 0 ≤ A * ((Y 1 + Y 2) - (G Y 1 + G Y 2)) := by
    have HL := rpow_div_le_core_loss hb0.le
      (add_nonneg (hwall 0).1.le (hwall 1).1.le) hk2 hc zero_lt_one hdec
    simp only [Real.rpow_one, one_mul] at HL
    exact HL.trans (mul_le_mul_of_nonneg_left (sub_le_sub_left hconn _) hA.le)
  refine ⟨hvalid, hT, horbit, hdrop, hnext, herr.trans ?_⟩
  calc
    _ = K * ((Y 1 + Y 2) / Y 0) := by ring
    _ ≤ K * (A * ((Y 1 + Y 2) - (G Y 1 + G Y 2))) := mul_le_mul_of_nonneg_left hpaid hK.le
    _ = (K * A) * ((Y 1 + Y 2) - (G Y 1 + G Y 2)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _)
      (sub_nonneg.mpr (add_le_add (hnext 0).2 (hnext 1).2))
