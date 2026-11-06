-- Prove2me | solution 1 for BianchiIX.partialCoreDownwardReturn_connection_domain
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T00:36:06.793202+00:00
-- url     : https://prove2.me/submissions/915fed1c-5c5e-4a64-a98d-80b46b86476a

import Definitions.Def_BianchiIX_Analysis_CoreGrowthBudget
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_CoreCoordinateDifferential
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreEntry
import Definitions.Def_BianchiIX_Dynamics_ConnectionExistence
import Definitions.Def_BianchiIX_Dynamics_ConnectionEvents
import Definitions.Def_BianchiIX_Dynamics_ConnectionReturn
import Definitions.Def_BianchiIX_EraReturnData
import Definitions.Def_BianchiIX_Dynamics_CoreConnectionChart
import Theorems.Thm_BianchiIX_connectionReturn_regular
import Theorems.Thm_BianchiIX_coreBootstrap_clock_bounds
import Theorems.Thm_BianchiIX_coreBootstrap_denom_lower
import Theorems.Thm_BianchiIX_coreBootstrap_original_clock_lower
import Theorems.Thm_BianchiIX_coreBootstrap_radius_closed
import Theorems.Thm_BianchiIX_exists_normalized_partialCore_return
import Theorems.Thm_BianchiIX_exists_partialCore_downward_radius_response
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_core_prefix_contraction
import Theorems.Thm_BianchiIX_normalized_core_residence
import Theorems.Thm_BianchiIX_normalized_core_return_downward
import Theorems.Thm_BianchiIX_normalized_core_return_isLeast
import Theorems.Thm_BianchiIX_normalized_partialCore_energy_band_improves
import Theorems.Thm_BianchiIX_normalized_wall_sign
import Theorems.Thm_BianchiIX_projectiveOriginalFlow_restart
import Theorems.Thm_BianchiIX_sech_le_exp
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.Module
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Normed.Operator.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreAngle_sqrt {m v : ℝ} (hv : 0 < v) :
    Real.sqrt (1 + ((1 - m) / v) ^ 2) = coreRadius m v / v := by
  apply (Real.sqrt_eq_iff_eq_sq (by positivity) (div_nonneg (coreRadius_pos hv).le hv.le)).mpr
  simp only [div_pow, coreRadius_sq]
  unfold coreEnergy
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.cosh_coreAngle {m v : ℝ} (hv : 0 < v) :
    Real.cosh (coreAngle m v) = coreRadius m v / v := by
  rw [coreAngle, Real.cosh_arsinh, coreAngle_sqrt hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.core_exit_connection_radial_range {k m : ℝ} (hk : 6 ≤ k) (hm : m < 1)
    (hE : |coreEnergy m 1 - k ^ 2| ≤ 1 / 8) : 4 ≤ -m ∧ k / 2 ≤ -m ∧ -m < k := by
  have hElo := (abs_le.mp hE).1
  have hEhi := (abs_le.mp hE).2
  dsimp [coreEnergy] at hElo hEhi
  have hm4 : 4 ≤ -m := by
    by_contra H
    have hm5 : 1 - m < 5 := by linarith only [H]
    have hs : (1 - m) ^ 2 < 5 ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hm] : 0 ≤ 1 - m) (by norm_num)).mpr hm5
    nlinarith only [hs, hElo, hk, sq_nonneg (k - 6)]
  refine ⟨hm4, ?_, ?_⟩
  · by_contra H
    have hs : (1 - m) ^ 2 < (k / 2 + 1) ^ 2 :=
      (sq_lt_sq₀ (by linarith only [hm] : 0 ≤ 1 - m) (by linarith only [hk])).mpr (by linarith only [H])
    nlinarith only [hs, hElo, hk, sq_nonneg (k - 6)]
  · by_contra H
    have hs : k ^ 2 ≤ (-m) ^ 2 := (sq_le_sq₀ (by linarith only [hk]) (by linarith only [hm4])).mpr (by linarith only [H])
    nlinarith only [hs, hEhi, hm4]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.partial_core_angle_gap {k z₀ z₁ Z : ℝ} (hk : 0 < k) (hZ : 0 ≤ Z)
    (hz₀ : z₀ ≤ Z) (hz₁ : 0 ≤ z₁)
    (hentry : Real.cosh Z ≤ k / 2) (hexit : 99 / 100 * k ≤ Real.cosh z₁) :
    Real.log (99 / 50 : ℝ) ≤ z₁ - z₀ ∧ 49 / 99 ≤ z₁ - z₀ ∧ 1 / 3 < z₁ - z₀ := by
  have horder : Z ≤ z₁ := by
    have H : Real.cosh Z ≤ Real.cosh z₁ := by linarith only [hentry, hexit, hk]
    simpa only [abs_of_nonneg hZ, abs_of_nonneg hz₁] using Real.cosh_le_cosh.mp H
  have H := sech_le_exp (neg_le_neg horder)
  rw [Real.cosh_neg, Real.cosh_neg, show -Z - -z₁ = z₁ - Z by ring] at H
  have H' : 1 / Real.cosh Z ≤ Real.exp (z₁ - Z) / Real.cosh z₁ := by
    simpa only [one_div_mul_eq_div] using H
  have Hmul := (div_le_div_iff₀ (Real.cosh_pos Z) (Real.cosh_pos z₁)).mp H'
  have Hratio : (99 / 50 : ℝ) ≤ Real.exp (z₁ - Z) := by
    apply (mul_le_mul_iff_right₀ (Real.cosh_pos Z)).mp
    nlinarith only [hentry, hexit, Hmul]
  have Hlog : Real.log (99 / 50 : ℝ) ≤ z₁ - Z :=
    (Real.log_le_iff_le_exp (by norm_num)).mpr Hratio
  have Hnum : (49 / 99 : ℝ) ≤ Real.log (99 / 50 : ℝ) := by
    have H := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 99 / 50)
    norm_num at H
    linarith only [H]
  refine ⟨by linarith only [Hlog, hz₀], by linarith only [Hnum, Hlog, hz₀], ?_⟩
  linarith only [Hnum, Hlog, hz₀]

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

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.toProjectiveState_wall_sign {x : NormalizedState} (hA : 0 < 1 + x 0) (i : Fin 3) :
    (toProjectiveState x i.succ = 0 ↔ wallValue i x = 0) ∧
      (0 ≤ toProjectiveState x i.succ ↔ 0 ≤ wallValue i x) := by
  have heq : toProjectiveState x i.succ = Real.sqrt 3 * wallValue i x / (1 + x 0) := by
    fin_cases i <;> rfl
  have hsqrt : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  rw [heq]
  constructor
  · simp only [div_eq_zero_iff, mul_eq_zero, ne_of_gt hsqrt, ne_of_gt hA, false_or, or_false]
  · rw [div_eq_mul_inv, mul_nonneg_iff_of_pos_right (inv_pos.mpr hA), mul_nonneg_iff_of_pos_left hsqrt]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_projective_wall_sign {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (β t i.succ = 0 ↔ β s i.succ = 0) ∧ (0 ≤ β t i.succ ↔ 0 ≤ β s i.succ) := by
  have H := normalized_wall_sign (convex_normalizedMaxDomain x t₀) (isOpen_normalizedMaxDomain x t₀)
    (fun _ hh => hasDerivAt_normalizedMaxCurve hh) hs ht i
  exact ⟨(toProjectiveState_wall_sign hAt i).1.trans (H.1.trans (toProjectiveState_wall_sign hAs i).1.symm),
    (toProjectiveState_wall_sign hAt i).2.trans (H.2.trans (toProjectiveState_wall_sign hAs i).2.symm)⟩

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_projective_wall_pos {x : NormalizedState} {t₀ s t : ℝ}
    (hs : s ∈ normalizedMaxDomain x t₀) (ht : t ∈ normalizedMaxDomain x t₀)
    (hAs : 0 < 1 + normalizedMaxCurve x t₀ s 0) (hAt : 0 < 1 + normalizedMaxCurve x t₀ t 0)
    (i : Fin 3) (hi : 0 < toProjectiveState (normalizedMaxCurve x t₀ s) i.succ) :
    0 < toProjectiveState (normalizedMaxCurve x t₀ t) i.succ := by
  have H := normalized_projective_wall_sign hs ht hAs hAt i
  have hne : toProjectiveState (normalizedMaxCurve x t₀ t) i.succ ≠ 0 :=
    fun h => (ne_of_gt hi) (H.1.mp h)
  exact lt_of_le_of_ne (H.2.mpr hi.le) hne.symm

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_normalized_partialCore_firstReturn {x : NormalizedState} {t₀ s k : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s)
    (hA : 0 < 1 + normalizedMaxCurve x t₀ s 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    coreRadius (β s 0) (β s 2) = k → (1 < β s 2 ∨ (β s 2 = 1 ∧ 1 ≤ β s 0)) →
    (0 ≤ β s 1 ∧ β s 1 ≤ (1 / 10000) / k) →
    (0 ≤ β s 2 * β s 3 ∧ β s 2 * β s 3 ≤ (1 / 10000) / k) →
    ∃ t > s, IsLeast {u | s < u ∧ β u 2 = 1} t ∧
      β t 0 < 1 ∧ 0 < coreAngle (β t 0) (β t 2) ∧
      deriv (fun u => β u 2) t ≤ -(1 + normalizedMaxCurve x t₀ t 0) * k / 2 ∧
      t - s ≤ 2 * k * Real.log (4 * k) ∧ ∀ u ∈ Icc s t,
        3 / (2 * k ^ 2) ≤ 1 + normalizedMaxCurve x t₀ u 0 ∧ coreRegion k (β u) ∧
        |coreRadius (β u 0) (β u 2) - k| ≤ 16 * (β s 1 + (β s 2 * β s 3) ^ 2 / k) ∧
        |coreRadius (β u 0) (β u 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro β hR hVcase hU hP
  obtain ⟨t, hst, hvt, H⟩ := exists_normalized_partialCore_return hc hk hs hA hR hVcase hU hP
  have hk0 : 0 < k := by linarith only [hk]
  have hpos (u : ℝ) (hu : u ∈ Icc s t) : 0 < 1 + normalizedMaxCurve x t₀ u 0 :=
    lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) (H u hu).1
  have hr (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_radius_bounds hk (H u hu).2
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 1 ≤ β u 2 := (H u hu).2.2.1
  have hwall (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_wall_bounds (H u hu).2
  have hleast := normalized_core_return_isLeast hc hk hs hst hpos
    (fun u hu => (hr u hu).1) hv (fun u hu => (hwall u hu).1) (fun u hu => (hwall u hu).2) hvt
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hdown := normalized_core_return_downward hc hk hs hst (hpos t htm) hvt
    (fun u hu => hv u ⟨hu.1.le, hu.2.le⟩) (hr t htm).1 (hwall t htm).1 (hwall t htm).2
  have htime := (normalized_core_residence hc hk hs hst.le hpos hr hv
    (fun u hu => (hwall u hu).1) (fun u hu => (hwall u hu).2)).2
  refine ⟨t, hst, hleast, hdown.1, hdown.2.1, hdown.2.2.1, htime, ?_⟩
  intro u hu
  have hsub : Icc s u ⊆ Icc s t := fun v hv => ⟨hv.1, hv.2.trans hu.2⟩
  have Henergy := normalized_partialCore_energy_band_improves hc hk hs hu.1
    (fun v hv => hpos v (hsub hv)) hR
    (fun v hv => by rw [coreRadius_sq]; exact (H v (hsub hv)).2.1)
    (fun v hv' => hv v (hsub hv')) (fun v hv => (H v (hsub hv)).2.2.2.1)
    (fun v hv => (H v (hsub hv)).2.2.2.2)
  exact ⟨(H u hu).1, (H u hu).2, Henergy⟩

end
end

section
noncomputable section
open BianchiIX
open Set

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

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.normalized_partialCore_exit_contraction {x : NormalizedState} {t₀ s t k Z : ℝ}
    (hc : stateConstraint x = 1) (hk : 6 ≤ k) (hs : t₀ ≤ s) (hst : s < t)
    (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hA : ∀ u ∈ Icc s t, 0 < 1 + normalizedMaxCurve x t₀ u 0) :
    let β := fun u => toProjectiveState (normalizedMaxCurve x t₀ u)
    (∀ u ∈ Icc s t, coreRegion k (β u)) →
    coreAngle (β s 0) (β s 2) ≤ Z → β t 2 = 1 →
    Real.log (99 / 50 : ℝ) ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      49 / 99 ≤ coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2) ∧
      β t 1 ≤ β s 1 * Real.exp (-k / 12) ∧ β t 3 ≤ β s 2 * β s 3 := by
  intro β hregion hz₀ hvt
  have hsm : s ∈ Icc s t := ⟨le_rfl, hst.le⟩
  have htm : t ∈ Icc s t := ⟨hst.le, le_rfl⟩
  have hk0 : 0 < k := by linarith only [hk]
  have hr (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_radius_bounds hk (hregion u hu)
  have hw (u : ℝ) (hu : u ∈ Icc s t) := coreRegion_wall_bounds (hregion u hu)
  have hv (u : ℝ) (hu : u ∈ Icc s t) : 1 ≤ β u 2 := (hregion u hu).2.1
  have hout := normalized_core_return_downward hc hk hs hst (hA t htm) hvt
    (fun u hu => hv u ⟨hu.1.le, hu.2.le⟩) (hr t htm).1 (hw t htm).1 (hw t htm).2
  have hcosh : 99 / 100 * k ≤ Real.cosh (coreAngle (β t 0) (β t 2)) := by
    rw [cosh_coreAngle (zero_lt_one.trans_le (hv t htm)), hvt, div_one]
    simpa only [hvt] using (hr t htm).1
  obtain ⟨hgap, hgap', hgap3⟩ := partial_core_angle_gap hk0 hZ hz₀ hout.2.1.le
    (by linarith only [hkZ]) hcosh
  have hdom : Icc s t ⊆ normalizedMaxDomain x t₀ := fun _ hu =>
    normalizedMaxDomain_contains_Ici_of_constraint hc t₀ (hs.trans hu.1)
  obtain ⟨hU, hP⟩ := normalized_core_prefix_contraction hk (convex_Icc s t) hdom hc hA
    hsm htm hst.le (fun u hu => (hr u hu).1) hv
    (fun u hu => (hw u hu).1) (fun u hu => (hw u hu).2)
  have hexp : -k * (coreAngle (β t 0) (β t 2) - coreAngle (β s 0) (β s 2)) / 4 ≤ -k / 12 := by
    have H := mul_le_mul_of_nonneg_left hgap3.le hk0.le
    linarith only [H]
  change β t 2 * β t 3 ≤ β s 2 * β s 3 at hP
  rw [hvt, one_mul] at hP
  exact ⟨hgap, hgap', hU.trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (hw s hsm).1.1), hP⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturnTime_eq {y : ProjectiveState} {T : ℝ}
    (hT : IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState y) 0 ∧
      projectiveOriginalFlow y 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState y) 0 t < 0} T) :
    partialCoreDownwardReturnTime y = T := hT.csInf_eq

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturnTime_eventuallyEq {y : ProjectiveState} {τ : ProjectiveState → ℝ}
    (hτ : ∀ᶠ z in 𝓝 y, IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
      projectiveOriginalFlow z 0 t 2 = 1 ∧
      normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0} (τ z)) :
    partialCoreDownwardReturnTime =ᶠ[𝓝 y] τ := hτ.mono fun _ h => partialCoreDownwardReturnTime_eq h

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.partialCoreDownwardReturn_regular {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    IsLeast {t | 0 < t ∧ projectiveOriginalFlow y 0 t 2 = 1} (partialCoreDownwardReturnTime y) ∧
      ContDiffAt ℝ 2 partialCoreDownwardReturnTime y ∧ ContDiffAt ℝ 2 partialCoreDownwardReturnState y ∧
      (∀ᶠ z in 𝓝 y,
        IsLeast {t | 0 < t ∧ t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          projectiveOriginalFlow z 0 t 2 = 1 ∧
          normalizedEventRate projectiveActiveWall (fromProjectiveState z) 0 t < 0}
            (partialCoreDownwardReturnTime z) ∧
        ∀ t ∈ Icc 0 (partialCoreDownwardReturnTime z), t ∈ normalizedMaxDomain (fromProjectiveState z) 0 ∧
          0 < 1 + normalizedMaxCurve (fromProjectiveState z) 0 t 0) ∧
      ∀ w : ProjectiveState,
        let v := fderiv ℝ toCoreAngleState y w
        let dz := fderiv ℝ projectiveCoreAngle y w
        |(fderiv ℝ partialCoreDownwardReturnState y w) 0 - v 0| ≤ 4096 * coreVariationBound *
          (|v 1| + (y 1 + y 2 * y 3) * (|v 0| + |v 2|) / k +
            (k * y 1 + (y 2 * y 3) ^ 2 / k) * |dz|) := by
  obtain ⟨T, _, hfirst, τ, hτ, hcτ, hnear, hcF, Hbound⟩ :=
    exists_partialCore_downward_radius_response hk hy hR hV
  have heq := partialCoreDownwardReturnTime_eventuallyEq (hnear.mono fun _ h => h.1)
  have hstate : partialCoreDownwardReturnState =ᶠ[𝓝 y] fun z =>
      toCoreAngleState (projectiveOriginalFlow z 0 (τ z)) := by
    filter_upwards [heq] with z hz
    simp only [partialCoreDownwardReturnState, hz]
  refine ⟨?_, hcτ.congr_of_eventuallyEq heq, hcF.congr_of_eventuallyEq hstate, ?_, ?_⟩
  · rw [heq.self_of_nhds, hτ]
    exact hfirst
  · filter_upwards [hnear, heq] with z hz ht
    simpa only [ht] using hz
  · intro w
    rw [hstate.fderiv_eq]
    exact Hbound w

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCoreDownwardReturn_bounds {k : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) :
    let T := partialCoreDownwardReturnTime y
    projectiveOriginalFlow y 0 T 0 < 1 ∧ T ≤ 2 * k * Real.log (4 * k) ∧
      ∀ t ∈ Icc 0 T,
        0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 t 0 ∧
        coreRegion k (projectiveOriginalFlow y 0 t) ∧
        |coreRadius (projectiveOriginalFlow y 0 t 0) (projectiveOriginalFlow y 0 t 2) - k| ≤
          16 * (y 1 + (y 2 * y 3) ^ 2 / k) ∧
        |coreRadius (projectiveOriginalFlow y 0 t 0) (projectiveOriginalFlow y 0 t 2) ^ 2 - k ^ 2| < 1 / 16 := by
  intro T
  have hk0 : 0 < k := by linarith only [hk]
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  let β := projectiveOriginalFlow y 0
  have hzero : β 0 = y := projectiveOriginalFlow_initial hD 0
  have hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 0 0 := by
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hR0 : coreRadius (β 0 0) (β 0 2) = k := by rw [hzero]; exact hR
  have hV0 : 1 < β 0 2 ∨ (β 0 2 = 1 ∧ 1 ≤ β 0 0) := by rw [hzero]; exact hV
  have hU0 : 0 ≤ β 0 1 ∧ β 0 1 ≤ (1 / 10000) / k := by rw [hzero]; exact hy.2.2.1
  have hP0 : 0 ≤ β 0 2 * β 0 3 ∧ β 0 2 * β 0 3 ≤ (1 / 10000) / k := by
    rw [hzero]; exact hy.2.2.2
  obtain ⟨S, _, hfirstS, hM, _, _, htime, H⟩ :=
    exists_normalized_partialCore_firstReturn hc hk le_rfl hA hR0 hV0 hU0 hP0
  have hST : S = T := hfirstS.unique (partialCoreDownwardReturn_regular hk hy hR hV).1
  rw [hST] at hM htime H
  refine ⟨hM, by simpa only [sub_zero] using htime, ?_⟩
  intro t ht
  have Ht := H t ht
  change _ ∧ _ ∧ |coreRadius (β t 0) (β t 2) - k| ≤
    16 * (β 0 1 + (β 0 2 * β 0 3) ^ 2 / k) ∧ _ at Ht
  rw [hzero] at Ht
  exact ⟨lt_of_lt_of_le (by positivity : 0 < 3 / (2 * k ^ 2)) Ht.1, Ht.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreExitConnectionParameters_phase {Z : CoreAngleState} (hK : 1 < Z 0) :
    phaseNorm (coreExitConnectionParameters Z 0 + 1) 1 = Z 0 := by
  have hs := Real.sq_sqrt (by nlinarith only [hK] : 0 ≤ Z 0 ^ 2 - 1)
  change Real.sqrt ((Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2) = Z 0
  rw [show (Real.sqrt (Z 0 ^ 2 - 1) - 1 + 1) ^ 2 + 1 ^ 2 = Z 0 ^ 2 by nlinarith only [hs]]
  exact Real.sqrt_sq (by linarith only [hK])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.coreExitConnectionParameters_of_exit {y : ProjectiveState} (hM : y 0 < 1) (hV : y 2 = 1) :
    coreExitConnectionParameters (toCoreAngleState y) = ![-y 0, y 1, y 3] := by
  have hs : (toCoreAngleState y 0) ^ 2 - 1 = (y 0 - 1) ^ 2 := by
    change coreRadius (y 0) (y 2) ^ 2 - 1 = _
    rw [coreRadius_sq, hV]
    dsimp [coreEnergy]
    ring
  ext i
  fin_cases i
  · change Real.sqrt ((toCoreAngleState y 0) ^ 2 - 1) - 1 = -y 0
    rw [hs, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hM] : y 0 - 1 < 0)]
    ring
  · rfl
  · change y 2 * y 3 = y 3
    rw [hV, one_mul]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.partialCoreDownwardReturn_contraction {k Z : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0))
    (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k) (hz : projectiveCoreAngle y ≤ Z) :
    let T := partialCoreDownwardReturnTime y
    projectiveOriginalFlow y 0 T 1 ≤ y 1 * Real.exp (-k / 12) ∧
      projectiveOriginalFlow y 0 T 3 ≤ y 2 * y 3 := by
  intro T
  have HR := partialCoreDownwardReturn_regular hk hy hR hV
  have HB := (partialCoreDownwardReturn_bounds hk hy hR hV).2.2
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hzero := projectiveOriginalFlow_initial hD (0 : ℝ)
  have hz0 : coreAngle (projectiveOriginalFlow y 0 0 0) (projectiveOriginalFlow y 0 0 2) ≤ Z := by
    rw [hzero]; exact hz
  have H := normalized_partialCore_exit_contraction hc hk le_rfl HR.1.1.1 hZ hkZ
    (fun t ht => (HB t ht).1) (fun t ht => (HB t ht).2.1) hz0 HR.1.1.2
  have HC := H.2.2
  change projectiveOriginalFlow y 0 T 1 ≤ projectiveOriginalFlow y 0 0 1 * Real.exp (-k / 12) ∧
    projectiveOriginalFlow y 0 T 3 ≤ projectiveOriginalFlow y 0 0 2 * projectiveOriginalFlow y 0 0 3 at HC
  rwa [hzero] at HC

end
end


/-- The fixed downward return enters a finite regular connection on the same exact orbit. -/
theorem solution {k Z ε : ℝ} {y : ProjectiveState}
    (hk : 6 ≤ k) (hy : coreRegion k y) (hR : coreRadius (y 0) (y 2) = k)
    (hV : 1 < y 2 ∨ (y 2 = 1 ∧ 1 ≤ y 0)) (hZ : 0 ≤ Z) (hkZ : 2 * Real.cosh Z ≤ k)
    (hz : projectiveCoreAngle y ≤ Z) (hε : 0 < ε ∧ ε ≤ 1 / 10000)
    (hu : 0 < y 1 ∧ y 1 ≤ ε / k) (hp : 0 < y 2 * y 3 ∧ y 2 * y 3 ≤ ε / k) :
    let T := partialCoreDownwardReturnTime y
    let out := projectiveOriginalFlow y 0 T
    let p := coreExitConnectionParameters (partialCoreDownwardReturnState y)
    out = connectionEntry (p 0) (p 1) (p 2) ∧
      (4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k) ∧
      (0 < p 1 ∧ p 1 ≤ ε / p 0) ∧ (0 < p 2 ∧ p 2 ≤ ε) ∧
      p 1 ≤ y 1 * Real.exp (-k / 12) ∧ p 2 ≤ y 2 * y 3 ∧
      phaseNorm (p 0 + 1) 1 = coreRadius (out 0) (out 2) ∧
      0 < 1 + normalizedMaxCurve (fromProjectiveState y) 0 T 0 ∧
      connectionReturnValid p ∧ ContDiffAt ℝ 2 connectionReturnTime p ∧
      ContDiffAt ℝ 2 connectionReturnState p ∧
      connectionReturnState p = projectiveOriginalFlow y 0 (T + connectionReturnTime p) := by
  intro T out p
  have hfirst := (partialCoreDownwardReturn_regular hk hy hR hV).1
  have HB := partialCoreDownwardReturn_bounds hk hy hR hV
  have hreg := HB.2.2
  have htm : T ∈ Icc 0 T := ⟨hfirst.1.1.le, le_rfl⟩
  have hr : coreRegion k out := (hreg T htm).2.1
  have hD := (coreRegion_clock_regular hk hy).1
  have hc := fromProjectiveState_constraint hD.ne'
  have hhit : out 2 = 1 := hfirst.1.2
  have hM : out 0 < 1 := HB.1
  have heq : p = ![-out 0, out 1, out 3] := coreExitConnectionParameters_of_exit hM hhit
  have hμ := core_exit_connection_radial_range hk hM (by simpa only [hhit] using hr.1)
  have hentry : out = connectionEntry (p 0) (p 1) (p 2) := by
    rw [heq]
    ext i
    fin_cases i <;> simp [connectionEntry, hhit]
  have hpos (i : Fin 3) (hi : 0 < y i.succ) : 0 < out i.succ := by
    apply normalized_projective_wall_pos (initial_mem_normalizedMaxDomain _ 0)
      (normalizedMaxDomain_contains_Ici_of_constraint hc 0 hfirst.1.1.le)
      (hreg 0 ⟨le_rfl, hfirst.1.1.le⟩).1 (hreg T htm).1 i
    change 0 < projectiveOriginalFlow y 0 0 i.succ
    rw [projectiveOriginalFlow_initial hD]
    exact hi
  have huout : 0 < out 1 := hpos 0 hu.1
  have hpout : 0 < out 3 := hpos 2 ((mul_pos_iff_of_pos_left (zero_lt_one.trans_le hy.2.1)).mp hp.1)
  have HC := partialCoreDownwardReturn_contraction hk hy hR hV hZ hkZ hz
  have huexp : y 1 * Real.exp (-k / 12) ≤ y 1 :=
    mul_le_of_le_one_right hu.1.le (Real.exp_le_one_iff.mpr (by linarith only [hk]))
  have hdomainU : 0 < p 1 ∧ p 1 ≤ ε / p 0 := by
    change 0 < out 1 ∧ out 1 ≤ ε / (p 0)
    refine ⟨huout, (HC.1.trans huexp).trans (hu.2.trans ?_)⟩
    rw [heq]
    exact div_le_div_of_nonneg_left hε.1.le
      (by simpa using lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hμ.1) hμ.2.2.le
  have hdomainP : 0 < p 2 ∧ p 2 ≤ ε := by
    change 0 < out 2 * out 3 ∧ out 2 * out 3 ≤ ε
    rw [hhit, one_mul]
    exact ⟨hpout, HC.2.trans (hp.2.trans (div_le_self hε.1.le (by linarith only [hk])))⟩
  have hμp : 4 ≤ p 0 ∧ k / 2 ≤ p 0 ∧ p 0 < k := by simpa only [heq, Matrix.cons_val_zero] using hμ
  have HR := connectionReturn_regular hμp.1
    ⟨hdomainU.1.le, hdomainU.2.trans (div_le_div_of_nonneg_right hε.2 (by linarith only [hμp.1]))⟩
    ⟨hdomainP.1, hdomainP.2.trans hε.2⟩
  refine ⟨hentry, hμp, hdomainU, hdomainP, HC.1, ?_, ?_, (hreg T htm).1,
    HR.1, HR.2.1, HR.2.2.1, ?_⟩
  · change out 2 * out 3 ≤ y 2 * y 3
    rw [hhit, one_mul]
    exact HC.2
  · apply coreExitConnectionParameters_phase
    exact lt_of_lt_of_le (by linarith only [hk] : 1 < 99 / 100 * k) (coreRegion_radius_bounds hk hr).1
  · have htc : 0 < connectionReturnTime p := HR.1.1.1.1
    have Hrestart := projectiveOriginalFlow_restart hD hfirst.1.1.le htc.le (hreg T htm).1
    change projectiveOriginalFlow (connectionEntry (p 0) (p 1) (p 2)) 0 (connectionReturnTime p) = _
    rw [← hentry]
    change projectiveOriginalFlow out 0 (connectionReturnTime p) =
      projectiveOriginalFlow y 0 (connectionReturnTime p + T) at Hrestart
    rwa [add_comm (connectionReturnTime p) T] at Hrestart
