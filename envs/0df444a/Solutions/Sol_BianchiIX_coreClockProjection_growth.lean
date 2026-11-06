-- Prove2me | solution 1 for BianchiIX.coreClockProjection_growth
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:42:45.442486+00:00
-- url     : https://prove2.me/submissions/6d851fd7-2f97-478a-8492-a897301c934f

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_CoreLinearization
import Definitions.Def_BianchiIX_Dynamics_CoreWeightedVariation
import Definitions.Def_BianchiIX_Dynamics_CoreFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Theorems.Thm_BianchiIX_coreBootstrap_angle_bound
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_coreGrowthPrimitive_difference
import Theorems.Thm_BianchiIX_coreRegion_variational_row_sums
import Theorems.Thm_BianchiIX_coreWeightedJacobian_mulVec
import Theorems.Thm_BianchiIX_hasDerivAt_coreAngle_scaled
import Theorems.Thm_BianchiIX_hasDerivAt_coreClockProjection
import Theorems.Thm_BianchiIX_hasDerivAt_coreGrowthPrimitive
import Theorems.Thm_BianchiIX_norm_le_exp_of_signedRowSum
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Data.Matrix.Mul
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue

noncomputable section
open BianchiIX
open Set

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreGrowthPrimitive_exp_difference {k a b : ℝ} (hk : 6 ≤ k)
    (ha : |a| ≤ Real.log (4 * k)) (hb : |b| ≤ Real.log (4 * k)) :
    Real.exp (coreGrowthPrimitive k b - coreGrowthPrimitive k a) ≤ coreVariationBound :=
  Real.exp_le_exp.mpr (coreGrowthPrimitive_difference hk ha hb)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreRadius_sq (m v : ℝ) : coreRadius m v ^ 2 = coreEnergy m v :=
  Real.sq_sqrt (by unfold coreEnergy; positivity)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_radius_bounds {k : ℝ} {y : ProjectiveState} (hk : 6 ≤ k) (hy : coreRegion k y) :
    99 / 100 * k ≤ coreRadius (y 0) (y 2) ∧ coreRadius (y 0) (y 2) ≤ 101 / 100 * k :=
  coreBootstrap_radius_closed hk (Real.sqrt_nonneg _)
    (by rw [coreRadius_sq]; exact hy.1)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreRegion_wall_bounds {k : ℝ} {y : ProjectiveState} (hy : coreRegion k y) :
    (0 ≤ y 1 ∧ y 1 ≤ (1 / 10000) / k) ∧ (0 ≤ y 3 ∧ y 3 ≤ (1 / 10000) / k) := by
  have hv0 : 0 < y 2 := lt_of_lt_of_le zero_lt_one hy.2.1
  have hw0 : 0 ≤ y 3 := (mul_nonneg_iff_of_pos_left hv0).mp hy.2.2.2.1
  exact ⟨hy.2.2.1, hw0, (le_mul_of_one_le_left hw0 hy.2.1).trans hy.2.2.2.2⟩

end
end

private theorem BianchiIX.signedRowSum_smul_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} {c : ℝ} (hc : 0 ≤ c) (i : ι) :
    signedRowSum (c • A) i = c * signedRowSum A i := by
  simp only [signedRowSum, Matrix.smul_apply, smul_eq_mul, abs_mul, abs_of_nonneg hc]
  rw [← Finset.mul_sum, ← mul_add]

private theorem BianchiIX.coreRegion_clock_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) :
    0 < projectiveStateDenom y ∧
      0 < coreClockFactor (coreRadius (y 0) (y 2)) (y 1) (y 3) ∧
        0 < coreOriginalClockRate y := by
  have hk0 : 0 < k := by linarith only [hk]
  have hr := coreRegion_radius_bounds hk hy
  obtain ⟨hu, hw⟩ := coreRegion_wall_bounds hy
  have hD := coreBootstrap_denom_lower (m := y 0) (v := y 2) hk hu hw
  have hd := (coreBootstrap_clock_bounds hk hr.1 hu hw).1
  have hrate := coreBootstrap_original_clock_lower hk hr (zero_le_one.trans hy.2.1) hu hw
  exact ⟨lt_of_lt_of_le (by norm_num) hD, lt_of_lt_of_le (by norm_num) hd,
    lt_of_lt_of_le (one_div_pos.mpr hk0) hrate⟩

private theorem BianchiIX.coreRegion_weighted_signedRowSum {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (i : Fin 3) :
    signedRowSum (coreWeightedJacobian k (projectiveCoreAngle y) (toCoreAngleState y)) i ≤
      2 / Real.cosh (projectiveCoreAngle y) + 24 * ((1 / 10000) / k) := by
  obtain ⟨h0, h1, h2⟩ := coreRegion_variational_row_sums hk hy
  have hb : 0 ≤ 2 / Real.cosh (projectiveCoreAngle y) + 24 * ((1 / 10000) / k) := by
    have hk0 : 0 < k := by linarith only [hk]
    positivity
  have hfin : (Finset.univ : Finset (Fin 3)) = {0, 1, 2} := by decide
  dsimp only [projectiveCoreAngle] at hb ⊢
  fin_cases i <;> simp [signedRowSum, hfin] <;> linarith only [h0, h1, h2, hb]

/-- The comparison can be made in original time, without differentiating an inverse clock. -/
theorem solution {beta v : ℝ → ProjectiveState} {k a b : ℝ}
    (hk : 6 ≤ k) (hab : a ≤ b)
    (hbeta : ∀ t ∈ Icc a b, HasDerivAt beta (projectiveOriginalField (beta t)) t)
    (hv : ∀ t ∈ Icc a b, HasDerivAt v (fderiv ℝ projectiveOriginalField (beta t) (v t)) t)
    (hregion : ∀ t ∈ Icc a b, coreRegion k (beta t)) :
    ‖scaleCoreVariation k (coreClockProjection (beta b) (v b))‖ ≤
      ‖scaleCoreVariation k (coreClockProjection (beta a) (v a))‖ * coreVariationBound := by
  have hk0 : 0 < k := by linarith only [hk]
  let xi := fun t => coreClockProjection (beta t) (v t)
  let theta := fun t => projectiveCoreAngle (beta t)
  let rate := fun t => coreOriginalClockRate (beta t)
  let f := fun t => scaleCoreVariation k (xi t)
  let A := fun t => rate t • coreWeightedJacobian k (theta t) (toCoreAngleState (beta t))
  have hxi (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt xi
      (rate t • (coreAngleJacobian (theta t) (toCoreAngleState (beta t))).mulVec (xi t)) t := by
    obtain ⟨hD, hd, _⟩ := coreRegion_clock_regular hk (hregion t ht)
    exact hasDerivAt_coreClockProjection (hbeta t ht) (hv t ht)
      (lt_of_lt_of_le zero_lt_one (hregion t ht).2.1) (ne_of_gt hD) (ne_of_gt hd)
  have hf (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt f ((A t).mulVec (f t)) t := by
    dsimp only [A, f]
    rw [Matrix.smul_mulVec, coreWeightedJacobian_mulVec (ne_of_gt hk0)]
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · exact hasDerivAt_pi.mp (hxi t ht) 0
    · apply ((hasDerivAt_pi.mp (hxi t ht) 1).const_mul k).congr_deriv
      change k * (rate t * _) = rate t * (k * _)
      ring
    · exact hasDerivAt_pi.mp (hxi t ht) 2
  have htheta (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt theta (rate t) t := by
    exact hasDerivAt_coreAngle_scaled (hbeta t ht) (lt_of_lt_of_le zero_lt_one (hregion t ht).2.1)
  have hZ (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => coreGrowthPrimitive k (theta s))
        ((2 / Real.cosh (theta t) + 24 * ((1 / 10000) / k)) * rate t) t :=
    (hasDerivAt_coreGrowthPrimitive k (theta t)).comp t (htheta t ht)
  have H := norm_le_exp_of_signedRowSum
    (fun t ht => (hf t ht).continuousAt.continuousWithinAt)
    (fun t ht => hf t (Ico_subset_Icc_self ht))
    (fun t ht => (hZ t ht).continuousAt.continuousWithinAt)
    (fun t ht => hZ t (Ico_subset_Icc_self ht))
    (fun t ht i => by
      have ht' := Ico_subset_Icc_self ht
      have hrate := (coreRegion_clock_regular hk (hregion t ht')).2.2.le
      dsimp only [A]
      rw [signedRowSum_smul_nonneg hrate]
      exact (mul_le_mul_of_nonneg_left (coreRegion_weighted_signedRowSum hk (hregion t ht') i)
        hrate).trans_eq (mul_comm _ _)) b ⟨hab, le_rfl⟩
  have hangle (t : ℝ) (ht : t ∈ Icc a b) : |theta t| ≤ Real.log (4 * k) :=
    coreBootstrap_angle_bound hk (coreRegion_radius_bounds hk (hregion t ht)).2 (hregion t ht).2.1
  exact H.trans (mul_le_mul_of_nonneg_left
    (coreGrowthPrimitive_exp_difference hk (hangle a ⟨le_rfl, hab⟩) (hangle b ⟨hab, le_rfl⟩))
    (norm_nonneg _))
