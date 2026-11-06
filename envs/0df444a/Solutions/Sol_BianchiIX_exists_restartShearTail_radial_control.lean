-- Prove2me | solution 1 for BianchiIX.exists_restartShearTail_radial_control
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-06T04:50:49.931338+00:00
-- url     : https://prove2.me/submissions/a748dac1-d0fb-4548-ab5d-f5dffc25d8f9

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_SectionRestartData
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_Linearization
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_FlowDifferential
import Definitions.Def_BianchiIX_Dynamics_FlowTransport
import Definitions.Def_BianchiIX_ShearTransportData
import Definitions.Def_BianchiIX_RadialTransportData
import Theorems.Thm_BianchiIX_abs_sub_le_integral_bound
import Theorems.Thm_BianchiIX_contDiff_normalizedField
import Theorems.Thm_BianchiIX_contDiff_stateConstraint
import Theorems.Thm_BianchiIX_exists_common_rpow_budget
import Theorems.Thm_BianchiIX_exists_restartShearFastEntry_control
import Theorems.Thm_BianchiIX_exists_restartShearTail_initial_variation
import Theorems.Thm_BianchiIX_exists_shearTail_variation_budget
import Theorems.Thm_BianchiIX_hasDerivAt_normalizedFlowDifferential
import Theorems.Thm_BianchiIX_hasDerivAt_normalized_components
import Theorems.Thm_BianchiIX_integral_le_of_dissipation
import Theorems.Thm_BianchiIX_le_exp_of_clock_deriv_le
import Theorems.Thm_BianchiIX_norm_le_exp_of_norm_deriv_budget
import Theorems.Thm_BianchiIX_normalizedConstraintDifferential_flow
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward
import Theorems.Thm_BianchiIX_normalizedMaxCurve_forward_of_constraint
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
import Theorems.Thm_BianchiIX_normalizedMaxCurve_shift
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_shearTail_constraint_bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.ProjIcc

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_moments_le_of_linear_dissipation {f f' : ℝ → ℝ} {a b c : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hdecay : ∀ t ∈ Icc a b, f' t ≤ -c * f t) (hfb : 0 ≤ f b) :
    (∫ t in a..b, f t) ≤ f a / c ∧ (∫ t in a..b, (t - a) * f t) ≤ f a / c ^ 2 := by
  have hcont := HasDerivAt.continuousOn hf
  refine ⟨integral_le_of_dissipation hab hc hf hcont hdecay hfb, ?_⟩
  have hd (t : ℝ) (ht : t ∈ Icc a b) :
      HasDerivAt (fun s => (1 + c * (s - a)) * f s)
        (c * f t + (1 + c * (t - a)) * f' t) t := by
    convert! ((((hasDerivAt_id t).sub_const a).const_mul c).const_add 1).mul (hf t ht) using 1
    simp
  have H := integral_le_of_dissipation (g := fun t => (t - a) * f t) hab (sq_pos_of_pos hc) hd
    ((continuousOn_id.sub continuousOn_const).mul hcont) (fun t ht => ?_) ?_
  · simpa only [sub_self, mul_zero, add_zero, one_mul] using H
  · have hta : 0 ≤ t - a := sub_nonneg.mpr ht.1
    have hfactor : 0 ≤ 1 + c * (t - a) := by positivity
    have H' := mul_le_mul_of_nonneg_left (hdecay t ht) hfactor
    nlinarith only [H']
  · exact mul_nonneg (by positivity) hfb

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.curvature_abs_le_sum_sq {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    |curvature a b c| ≤ (a + b + c) ^ 2 := by
  rw [abs_le]
  constructor
  · unfold curvature
    nlinarith [sq_nonneg a, sq_nonneg b, sq_nonneg c]
  · unfold curvature
    nlinarith [mul_nonneg ha hb, mul_nonneg hb hc, mul_nonneg hc ha]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.norm_le_exp_integral_of_norm_deriv {f f' : ℝ → E} {k e : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hk : ContinuousOn k (Icc a b)) (he : ContinuousOn e (Icc a b))
    (hk0 : ∀ t ∈ Icc a b, 0 ≤ k t) (he0 : ∀ t ∈ Icc a b, 0 ≤ e t)
    (hbound : ∀ t ∈ Icc a b, ‖f' t‖ ≤ k t * ‖f t‖ + e t) :
    ‖f b‖ ≤ (‖f a‖ + ∫ t in a..b, e t) * Real.exp (∫ t in a..b, k t) := by
  let K : ℝ → ℝ := fun t => k (projIcc a b hab t)
  let R : ℝ → ℝ := fun t => e (projIcc a b hab t)
  let z : ℝ → ℝ := fun t => ∫ u in a..t, K u
  let B : ℝ → ℝ := fun t => ‖f a‖ + ∫ u in a..t, R u
  have hK : Continuous K := hk.domRestrict.comp continuous_projIcc
  have hR : Continuous R := he.domRestrict.comp continuous_projIcc
  have hKe (t : ℝ) (ht : t ∈ Icc a b) : K t = k t := by simp only [K, projIcc_of_mem hab ht]
  have hRe (t : ℝ) (ht : t ∈ Icc a b) : R t = e t := by simp only [R, projIcc_of_mem hab ht]
  have hz (t : ℝ) : HasDerivAt z (K t) t := intervalIntegral.integral_hasDerivAt_right
    (hK.intervalIntegrable _ _) hK.stronglyMeasurable.stronglyMeasurableAtFilter hK.continuousAt
  have hB (t : ℝ) : HasDerivAt B (R t) t := (intervalIntegral.integral_hasDerivAt_right
    (hR.intervalIntegrable _ _) hR.stronglyMeasurable.stronglyMeasurableAtFilter hR.continuousAt).const_add _
  have hBn (t : ℝ) (ht : t ∈ Icc a b) : 0 ≤ B t := add_nonneg (norm_nonneg _)
    (intervalIntegral.integral_nonneg ht.1 (fun u hu => by rw [hRe u ⟨hu.1, hu.2.trans ht.2⟩]; exact he0 u ⟨hu.1, hu.2.trans ht.2⟩))
  have H := norm_le_exp_of_norm_deriv_budget hf (fun t _ => hz t) (fun t _ => hB t) hBn
    (fun t ht => by rw [hRe t ht]; exact he0 t ht) (by simp [B])
    (fun t ht => by
      simp only [z, intervalIntegral.integral_same]
      exact intervalIntegral.integral_nonneg ht.1 (fun u hu => by
        rw [hKe u ⟨hu.1, hu.2.trans ht.2⟩]; exact hk0 u ⟨hu.1, hu.2.trans ht.2⟩))
    (fun t ht => by rw [hKe t ht, hRe t ht]; exact hbound t ht) b ⟨hab, le_rfl⟩
  have HK : (∫ t in a..b, K t) = ∫ t in a..b, k t := intervalIntegral.integral_congr
    (fun t ht => hKe t (uIcc_of_le hab ▸ ht))
  have HR : (∫ t in a..b, R t) = ∫ t in a..b, e t := intervalIntegral.integral_congr
    (fun t ht => hRe t (uIcc_of_le hab ▸ ht))
  simpa only [B, z, intervalIntegral.integral_same, sub_zero, HK, HR] using H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_wall_rates {a p s n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hp : p < 0)
    (hs : a / 2 ≤ s ∧ s ≤ 3 * a)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16) (hc : constraint p s n x y = 1) :
    rateOne p s ≤ -2 ∧ |rateTwo p s| ≤ 6 * a ∧ rateThree p s ≤ -a / 2 := by
  obtain ⟨hQ, _, _, _, hp', hAl, hAu⟩ := shearTail_constraint_bounds ha hp hs hn hx hy hc
  have HC : p ^ 2 + s ^ 2 + curvature n x y = 1 := hc
  have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
  have hs0 : 0 ≤ s := by linarith only [hs.1, ha.1]
  have hr0 := Real.sqrt_nonneg (3 : ℝ)
  have hr2 := Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)
  have hrl : (3 : ℝ) / 2 ≤ Real.sqrt 3 := by nlinarith only [hr0, hr2]
  have hru : Real.sqrt 3 ≤ (7 : ℝ) / 4 := by nlinarith only [hr0, hr2]
  have hRslo := mul_le_mul hrl hs.1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 2) hr0
  have hRshi := mul_le_mul hru hs.2 hs0 (by norm_num : (0 : ℝ) ≤ 7 / 4)
  refine ⟨?_, abs_le.mpr ⟨?_, ?_⟩, ?_⟩
  · dsimp only [rateOne, shearSq]
    nlinarith only [hp', sq_nonneg (p + 15 / 16), sq_nonneg s]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).1, hAu, hRslo, ha2, ha.1]
  · dsimp only [rateTwo, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRshi, ha2, ha.1, sq_nonneg a]
  · dsimp only [rateThree, shearSq]
    nlinarith only [HC, (abs_le.mp hQ).2, hAl, hRslo, ha2, ha.1, sq_nonneg a]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_shear_rate {a s n x y : ℝ}
    (ha : 0 ≤ a ∧ a ≤ 1 / 256) (hs : |s| ≤ 3 * a)
    (hn : 0 ≤ n) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    |shearMinus s n x y| ≤ 3 * (x ^ 2 + y ^ 2 + n * (x + y) + a * n ^ 2) := by
  have hQ : |curvature n x y| ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y) := by
    apply abs_le.mpr
    dsimp only [curvature]
    constructor
    · nlinarith only [sq_nonneg n, sq_nonneg (x - y)]
    · nlinarith only [mul_nonneg hx hy, mul_nonneg hn (add_nonneg hx hy)]
  have hH : |-x ^ 2 + y ^ 2 + n * x - n * y| ≤ x ^ 2 + y ^ 2 + n * (x + y) := by
    apply abs_le.mpr
    constructor <;> nlinarith only [sq_nonneg x, sq_nonneg y, mul_nonneg hn hx, mul_nonneg hn hy]
  have hr : |Real.sqrt 3| ≤ (2 : ℝ) := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have HQ := mul_le_mul hQ hs (abs_nonneg _) (by positivity : 0 ≤ n ^ 2 + x ^ 2 + y ^ 2 + 2 * n * (x + y))
  have HH := mul_le_mul hr hH (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 2)
  have H := abs_add_le (curvature n x y * s) (Real.sqrt 3 * (-x ^ 2 + y ^ 2 + n * x - n * y))
  rw [abs_mul, abs_mul] at H
  have Hsmall := mul_nonneg (show 0 ≤ 1 - 6 * a by linarith only [ha.2])
    (show 0 ≤ x ^ 2 + y ^ 2 + n * (x + y) by positivity)
  dsimp only [shearMinus]
  nlinarith only [H, HQ, HH, Hsmall, mul_nonneg ha.1 (add_nonneg (sq_nonneg x) (sq_nonneg y))]

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology NNReal

private theorem BianchiIX.hasFDerivAt_normalizedField (x : NormalizedState) :
    HasFDerivAt normalizedField (normalizedDifferential x) x :=
  ((contDiff_normalizedField 1).differentiable (by norm_num) x).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasFDerivAt_normalizedMaxCurve_initial {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    HasFDerivAt (fun y => normalizedMaxCurve y t₀ t) (normalizedFlowDifferential x t₀ t) x := by
  have H := (normalizedMaxCurve_regular ht).2.comp x (contDiffAt_id.prodMk contDiffAt_const)
  exact (H.differentiableAt (by norm_num)).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasFDerivAt_stateConstraint (x : NormalizedState) :
    HasFDerivAt stateConstraint (normalizedConstraintDifferential x) x :=
  ((contDiff_stateConstraint 1).differentiable (by norm_num) x).hasFDerivAt

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTail_polynomials {α : ℝ → NormalizedState} {v : NormalizedState} {t : ℝ}
    (hα : HasDerivAt α v t) :
    HasDerivAt (fun u => curvature (α u 2) (α u 3) (α u 4)) (shearTailCurvatureDifferential (α t) v) t ∧
    HasDerivAt (fun u => -(α u 3) ^ 2 + (α u 4) ^ 2 + α u 2 * α u 3 - α u 2 * α u 4)
      (shearTailCouplingDifferential (α t) v) t := by
  have hn := hasDerivAt_pi.mp hα 2
  have hx := hasDerivAt_pi.mp hα 3
  have hy := hasDerivAt_pi.mp hα 4
  constructor
  · convert! (((hn.pow 2).add (hx.pow 2)).add (hy.pow 2)).sub
      ((((hn.mul hx).add (hx.mul hy)).add (hy.mul hn)).const_mul 2) using 1
    dsimp only [shearTailCurvatureDifferential]
    ring
  · convert! ((((hx.pow 2).neg.add (hy.pow 2)).add (hn.mul hx)).sub (hn.mul hy)) using 1
    dsimp only [shearTailCouplingDifferential]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedConstraintDifferential_shearTail (z v : NormalizedState) :
    normalizedConstraintDifferential z v = 2 * z 0 * v 0 + 2 * z 1 * v 1 +
      shearTailCurvatureDifferential z v := by
  let α : ℝ → NormalizedState := fun t i => z i + t * v i
  have hα : HasDerivAt α v 0 := hasDerivAt_pi.mpr (fun i => by
    simpa only [one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (v i)).const_add (z i))
  have hz : α 0 = z := by ext i; simp [α]
  have H := (hasFDerivAt_stateConstraint (α 0)).comp_hasDerivAt 0 hα
  have HQ := (hasDerivAt_shearTail_polynomials hα).1
  have H' := (((hasDerivAt_pi.mp hα 0).pow 2).add ((hasDerivAt_pi.mp hα 1).pow 2)).add HQ
  change HasDerivAt (fun t => stateConstraint (α t)) _ 0 at H'
  have HE := H.unique H'
  rw [hz] at HE
  convert! HE using 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedDifferential_shearTail (z v : NormalizedState) :
    normalizedDifferential z v 1 = curvature (z 2) (z 3) (z 4) * v 1 +
      z 1 * shearTailCurvatureDifferential z v + Real.sqrt 3 * shearTailCouplingDifferential z v ∧
    normalizedDifferential z v 2 = (-2 * z 0 * v 0 - 2 * z 1 * v 1 + 2 * v 0) * z 2 +
      rateOne (z 0) (z 1) * v 2 ∧
    normalizedDifferential z v 3 = (-2 * z 0 * v 0 - 2 * z 1 * v 1 - v 0 + Real.sqrt 3 * v 1) * z 3 +
      rateTwo (z 0) (z 1) * v 3 ∧
    normalizedDifferential z v 4 = (-2 * z 0 * v 0 - 2 * z 1 * v 1 - v 0 - Real.sqrt 3 * v 1) * z 4 +
      rateThree (z 0) (z 1) * v 4 := by
  let α : ℝ → NormalizedState := fun t i => z i + t * v i
  have hα : HasDerivAt α v 0 := hasDerivAt_pi.mpr (fun i => by
    simpa only [one_mul] using ((hasDerivAt_id' (0 : ℝ)).mul_const (v i)).const_add (z i))
  have hz : α 0 = z := by ext i; simp [α]
  have HD := (hasFDerivAt_normalizedField (α 0)).comp_hasDerivAt 0 hα
  have H (i : Fin 5) := hasDerivAt_pi.mp HD i
  obtain ⟨HQ, HH⟩ := hasDerivAt_shearTail_polynomials hα
  have Hp := hasDerivAt_pi.mp hα 0
  have Hs := hasDerivAt_pi.mp hα 1
  have Hshear := (HQ.mul Hs).add (HH.const_mul (Real.sqrt 3))
  have Hr := ((Hp.pow 2).add (Hs.pow 2)).neg
  have Hn := (Hr.add (Hp.const_mul 2)).mul (hasDerivAt_pi.mp hα 2)
  have Hx := ((Hr.sub Hp).add (Hs.const_mul (Real.sqrt 3))).mul (hasDerivAt_pi.mp hα 3)
  have Hy := ((Hr.sub Hp).sub (Hs.const_mul (Real.sqrt 3))).mul (hasDerivAt_pi.mp hα 4)
  have H1 := (H 1).unique Hshear
  have H2 := (H 2).unique Hn
  have H3 := (H 3).unique Hx
  have H4 := (H 4).unique Hy
  simp only [Pi.add_apply, Pi.sub_apply, Pi.neg_apply, Pi.pow_apply, hz] at H1 H2 H3 H4
  refine ⟨?_, ?_, ?_, ?_⟩
  · convert! H1 using 1
    ring
  · convert! H2 using 1
    dsimp only [rateOne, shearSq]
    ring
  · convert! H3 using 1
    dsimp only [rateTwo, shearSq]
    ring
  · convert! H4 using 1
    dsimp only [rateThree, shearSq]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_shearTailVariation {α v : ℝ → NormalizedState} {t : ℝ}
    (hα : HasDerivAt α (normalizedField (α t)) t)
    (hv : HasDerivAt v (normalizedDifferential (α t) (v t)) t)
    (hc : normalizedConstraintDifferential (α t) (v t) = 0)
    (hp : α t 0 ≠ 0) (hn : α t 2 ≠ 0) (hx : α t 3 ≠ 0) (hy : α t 4 ≠ 0) :
    HasDerivAt (fun u => shearTailVariation (α u) (v u)) (shearTailVariationRate (α t) (v t)) t := by
  rw [normalizedConstraintDifferential_shearTail] at hc
  have Hvp : v t 0 = (α t 1 * v t 1 + shearTailCurvatureDifferential (α t) (v t) / 2) / (-α t 0) := by
    apply (eq_div_iff (neg_ne_zero.mpr hp)).mpr
    nlinarith only [hc]
  obtain ⟨HS, HN, HX, HY⟩ := normalizedDifferential_shearTail (α t) (v t)
  obtain ⟨_, _, Hn, Hx, Hy⟩ := hasDerivAt_normalized_components hα
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · convert! hasDerivAt_pi.mp hv 1 using 1
    exact HS.symm
  · convert! (hasDerivAt_pi.mp hv 2).div Hn hn using 1
    dsimp [shearTailVariationRate]
    rw [HN, Hvp]
    field_simp [hp, hn]
    ring
  · convert! (hasDerivAt_pi.mp hv 3).div Hx hx using 1
    dsimp [shearTailVariationRate]
    rw [HX, Hvp]
    field_simp [hp, hx]
    ring
  · convert! (hasDerivAt_pi.mp hv 4).div Hy hy using 1
    dsimp [shearTailVariationRate]
    rw [HY, Hvp]
    field_simp [hp, hy]
    ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.normalizedFlow_shearTailVariation {z v : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain z t₀) (hc : normalizedConstraintDifferential z v = 0)
    (hp : normalizedMaxCurve z t₀ t 0 ≠ 0)
    (hn : normalizedMaxCurve z t₀ t 2 ≠ 0) (hx : normalizedMaxCurve z t₀ t 3 ≠ 0)
    (hy : normalizedMaxCurve z t₀ t 4 ≠ 0) :
    HasDerivAt (fun u => shearTailVariation (normalizedMaxCurve z t₀ u) (normalizedFlowDifferential z t₀ u v))
      (shearTailVariationRate (normalizedMaxCurve z t₀ t) (normalizedFlowDifferential z t₀ t v)) t := by
  have Hv := (hasDerivAt_normalizedFlowDifferential ht).clm_apply (hasDerivAt_const t v)
  have Hc := congrArg (fun L : NormalizedState →L[ℝ] ℝ => L v) (normalizedConstraintDifferential_flow ht)
  simp only [ContinuousLinearMap.comp_apply, hc] at Hc
  apply hasDerivAt_shearTailVariation (hasDerivAt_normalizedMaxCurve ht) _ Hc hp hn hx hy
  simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.map_zero, add_zero] using Hv

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.le_exp_of_linear_deriv_le {I : Set ℝ} (hI : Convex ℝ I)
    {f f' : ℝ → ℝ} {c s t : ℝ}
    (hf : ∀ u ∈ I, HasDerivAt f (f' u) u) (hbound : ∀ u ∈ I, f' u ≤ c * f u)
    (hs : s ∈ I) (ht : t ∈ I) (hst : s ≤ t) :
    f t ≤ f s * Real.exp (c * (t - s)) := by
  exact le_exp_of_clock_deriv_le hI hf (fun u _ => hasDerivAt_id u)
    (fun u hu => by simpa only [mul_one] using hbound u hu) hs ht hst

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.abs_sub_le_of_deriv_primitive {f f' z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (f' t) t)
    (hz : ∀ t ∈ Icc a b, HasDerivAt z (z' t) t)
    (hb : ∀ t ∈ Icc a b, |f' t| ≤ z' t) :
    ∀ t ∈ Icc a b, |f t - f a| ≤ z t - z a := by
  intro t ht
  have ha : a ∈ Icc a b := ⟨le_rfl, ht.1.trans ht.2⟩
  have HU := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [le_abs_self (f' s), hb s hs]) ha ht ht.1
  have HL := le_exp_of_linear_deriv_le (convex_Icc a b) (fun s hs => (hf s hs).neg.sub (hz s hs)) (c := 0)
    (fun s hs => by nlinarith only [neg_le_abs (f' s), hb s hs]) ha ht ht.1
  simp only [zero_mul, Real.exp_zero, mul_one, Pi.sub_apply, Pi.neg_apply] at HU HL
  exact abs_le.mpr ⟨by linarith only [HL], by linarith only [HU]⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.two_moment_variation_bound {s s' b : ℝ → ℝ} {l l' : ℝ → E} {T : ℝ}
    (hT : 0 ≤ T) (hs : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt s (s' t) t)
    (hl : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt l (l' t) t)
    (hb : ContinuousOn b (Icc (0 : ℝ) T)) (hb0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ b t)
    (hds : ∀ t ∈ Icc (0 : ℝ) T, |s' t| ≤ 2 * b t * |s t| + 4 * b t * ‖l t‖)
    (hdl : ∀ t ∈ Icc (0 : ℝ) T, ‖l' t‖ ≤ 2 * |s t| + 9 * b t * ‖l t‖) :
    let J₀ := ∫ t in 0..T, b t
    let J₁ := ∫ t in 0..T, t * b t
    let c := Real.exp (9 * J₀)
    let B := (|s 0| + 4 * c * ‖l 0‖ * J₀) * Real.exp (2 * J₀ + 8 * c * J₁)
    ∀ t ∈ Icc (0 : ℝ) T, |s t| ≤ B ∧ ‖l t‖ ≤ c * (‖l 0‖ + 2 * t * B) := by
  intro J₀ J₁ c B
  have hc : 0 ≤ c := (Real.exp_pos _).le
  have hsc := (HasDerivAt.continuousOn hs).abs
  have hlc := (HasDerivAt.continuousOn hl).norm
  let F : ℝ → ℝ := fun t => 2 * b t * |s t| + 4 * b t * ‖l t‖
  have hF : ContinuousOn F (Icc (0 : ℝ) T) :=
    ((hb.const_mul 2).mul hsc).add ((hb.const_mul 4).mul hlc)
  have hF0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ F t := by
    dsimp only [F]; positivity [hb0 t ht]
  let G : ℝ → ℝ := fun t => F (projIcc 0 T hT t)
  let S : ℝ → ℝ := fun t => |s 0| + ∫ u in 0..t, G u
  have hG : Continuous G := hF.domRestrict.comp continuous_projIcc
  have hGe (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : G t = F t := by simp only [G, projIcc_of_mem hT ht]
  have hS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt S (F t) t := by
    rw [← hGe t ht]
    exact (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable _ _)
      hG.stronglyMeasurable.stronglyMeasurableAtFilter hG.continuousAt).const_add _
  have hSi : S 0 = |s 0| := by simp [S]
  have hSm : MonotoneOn S (Icc (0 : ℝ) T) :=
    monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 T) (HasDerivAt.continuousOn hS)
      (fun t ht => (hS t (interior_subset ht)).hasDerivWithinAt)
      (fun t ht => hF0 t (interior_subset ht))
  have hS0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ S t :=
    (abs_nonneg (s 0)).trans (hSi ▸ hSm ⟨le_rfl, hT⟩ ht ht.1)
  have hsS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : |s t| ≤ S t := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
    have H := abs_sub_le_integral_bound ht.1 (fun u hu => hs u (hsub hu)) (hF.mono hsub)
      (fun u hu => hds u (hsub hu))
    have HI : (∫ u in 0..t, G u) = ∫ u in 0..t, F u := intervalIntegral.integral_congr
      (fun u hu => hGe u (hsub (uIcc_of_le ht.1 ▸ hu)))
    dsimp only [S]
    rw [HI]
    have HA := abs_add_le (s t - s 0) (s 0)
    rw [sub_add_cancel] at HA
    linarith only [HA, H]
  have Hprefix {g : ℝ → ℝ} (hg : ContinuousOn g (Icc (0 : ℝ) T))
      (hg0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ g t) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      (∫ u in 0..t, g u) ≤ ∫ u in 0..T, g u :=
    intervalIntegral.integral_mono_interval le_rfl ht.1 ht.2
      (ae_restrict_of_forall_mem measurableSet_Ioc (fun u hu => hg0 u ⟨hu.1.le, hu.2⟩))
      (hg.intervalIntegrable_of_Icc hT)
  have hlS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖l t‖ ≤ c * (‖l 0‖ + 2 * t * S t) := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
    have H := norm_le_exp_integral_of_norm_deriv ht.1 (fun u hu => hl u (hsub hu))
      ((hb.const_mul 9).mono hsub) ((hsc.const_mul 2).mono hsub)
      (fun u hu => by positivity [hb0 u (hsub hu)]) (fun u _ => by positivity)
      (fun u hu => by linarith only [hdl u (hsub hu)])
    have HB : (∫ u in 0..t, 2 * |s u|) ≤ 2 * t * S t := by
      have HI : (∫ u in 0..t, 2 * |s u|) ≤ ∫ _u in 0..t, 2 * S t := intervalIntegral.integral_mono_on ht.1
        (((hsc.const_mul 2).mono hsub).intervalIntegrable_of_Icc ht.1)
        (continuous_const.intervalIntegrable 0 t)
        (fun u hu => mul_le_mul_of_nonneg_left ((hsS u (hsub hu)).trans (hSm (hsub hu) ht hu.2)) (by norm_num : (0 : ℝ) ≤ 2))
      simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul, mul_left_comm, mul_assoc] using HI
    have HE : Real.exp (∫ u in 0..t, 9 * b u) ≤ c := by
      rw [intervalIntegral.integral_const_mul]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (Hprefix hb hb0 t ht) (by norm_num))
    have HP := mul_le_mul (add_le_add le_rfl HB) HE (Real.exp_pos _).le
      (by positivity [hS0 t ht, ht.1] : 0 ≤ ‖l 0‖ + 2 * t * S t)
    exact H.trans (HP.trans_eq (mul_comm _ _))
  let k : ℝ → ℝ := fun t => (2 + 8 * c * t) * b t
  let e : ℝ → ℝ := fun t => 4 * c * ‖l 0‖ * b t
  have hk : ContinuousOn k (Icc (0 : ℝ) T) := (continuousOn_const.add (continuousOn_const.mul continuousOn_id)).mul hb
  have he : ContinuousOn e (Icc (0 : ℝ) T) := hb.const_mul _
  have hk0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ k t := by dsimp only [k]; positivity [hb0 t ht, ht.1]
  have he0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ e t := by dsimp only [e]; positivity [hb0 t ht]
  have HdS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : ‖F t‖ ≤ k t * ‖S t‖ + e t := by
    rw [Real.norm_eq_abs, abs_of_nonneg (hF0 t ht), Real.norm_eq_abs, abs_of_nonneg (hS0 t ht)]
    dsimp only [F, k, e]
    have H1 := mul_le_mul_of_nonneg_left (hsS t ht) (by positivity [hb0 t ht] : 0 ≤ 2 * b t)
    have H2 := mul_le_mul_of_nonneg_left (hlS t ht) (by positivity [hb0 t ht] : 0 ≤ 4 * b t)
    nlinarith only [H1, H2]
  have Hk : (∫ t in 0..T, k t) = 2 * J₀ + 8 * c * J₁ := by
    have H : k = fun t => 2 * b t + (8 * c) * (t * b t) := by ext t; dsimp only [k]; ring
    have HI₁ : IntervalIntegrable (fun t => 2 * b t) volume 0 T := (hb.const_mul 2).intervalIntegrable_of_Icc hT
    have HI₂ : IntervalIntegrable (fun t => 8 * c * (t * b t)) volume 0 T :=
      ((continuousOn_id.mul hb).const_mul (8 * c)).intervalIntegrable_of_Icc hT
    rw [H, intervalIntegral.integral_add HI₁ HI₂,
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have He : (∫ t in 0..T, e t) = 4 * c * ‖l 0‖ * J₀ := intervalIntegral.integral_const_mul _ _
  have HSB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : S t ≤ B := by
    have hsub : Icc (0 : ℝ) t ⊆ Icc (0 : ℝ) T := Icc_subset_Icc_right ht.2
    have H := norm_le_exp_integral_of_norm_deriv ht.1 (fun u hu => hS u (hsub hu))
      (hk.mono hsub) (he.mono hsub) (fun u hu => hk0 u (hsub hu)) (fun u hu => he0 u (hsub hu))
      (fun u hu => HdS u (hsub hu))
    rw [Real.norm_eq_abs, abs_of_nonneg (hS0 t ht), hSi, Real.norm_eq_abs, abs_abs] at H
    have HE := Hprefix he he0 t ht
    have HK := Hprefix hk hk0 t ht
    rw [He] at HE
    rw [Hk] at HK
    have hJ₀ : 0 ≤ J₀ := intervalIntegral.integral_nonneg hT hb0
    exact H.trans (mul_le_mul (add_le_add le_rfl HE) (Real.exp_le_exp.mpr HK) (Real.exp_pos _).le
      (by positivity : 0 ≤ |s 0| + 4 * c * ‖l 0‖ * J₀))
  intro t ht
  refine ⟨(hsS t ht).trans (HSB t ht), (hlS t ht).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (add_le_add le_rfl
    (mul_le_mul_of_nonneg_left (HSB t ht) (by positivity [ht.1] : 0 ≤ 2 * t))) hc

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

private theorem BianchiIX.two_moment_variation_small {s s' b : ℝ → ℝ} {l l' : ℝ → E} {T : ℝ}
    (hT : 0 ≤ T) (hs : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt s (s' t) t)
    (hl : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt l (l' t) t)
    (hb : ContinuousOn b (Icc (0 : ℝ) T)) (hb0 : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ b t)
    (hds : ∀ t ∈ Icc (0 : ℝ) T, |s' t| ≤ 2 * b t * |s t| + 4 * b t * ‖l t‖)
    (hdl : ∀ t ∈ Icc (0 : ℝ) T, ‖l' t‖ ≤ 2 * |s t| + 9 * b t * ‖l t‖)
    (hinit : |s 0| ≤ 2)
    (hsmall : 9 * (∫ t in 0..T, b t) ≤ Real.log 2 ∧
      2 * (∫ t in 0..T, b t) + 16 * (∫ t in 0..T, t * b t) ≤ 1 / 2 ∧
      ‖l 0‖ * (∫ t in 0..T, b t) ≤ 1 / 16) :
    ∀ t ∈ Icc (0 : ℝ) T, |s t| ≤ 5 ∧ ‖l t‖ ≤ 2 * ‖l 0‖ + 20 * t := by
  let J₀ := ∫ t in 0..T, b t
  let J₁ := ∫ t in 0..T, t * b t
  let c := Real.exp (9 * J₀)
  have hc0 : 0 ≤ c := (Real.exp_pos _).le
  have hc : c ≤ 2 := (Real.exp_le_exp.mpr hsmall.1).trans_eq (Real.exp_log (by norm_num))
  have hJ₀ : 0 ≤ J₀ := intervalIntegral.integral_nonneg hT hb0
  have hJ₁ : 0 ≤ J₁ := intervalIntegral.integral_nonneg hT (fun t ht => mul_nonneg ht.1 (hb0 t ht))
  have Hexp : Real.exp (2 * J₀ + 8 * c * J₁) ≤ 2 := by
    have He := Real.exp_lt_two_add_div_two_sub (x := (1 : ℝ) / 2) (by norm_num) (by norm_num)
    norm_num at He
    apply (Real.exp_le_exp.mpr (show 2 * J₀ + 8 * c * J₁ ≤ 1 / 2 by
      nlinarith only [hsmall.2.1, mul_le_mul_of_nonneg_right hc hJ₁])).trans
    linarith only [He]
  have Hfac : |s 0| + 4 * c * ‖l 0‖ * J₀ ≤ 5 / 2 := by
    have H := mul_le_mul hc hsmall.2.2 (mul_nonneg (norm_nonneg _) hJ₀) (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [H, hinit]
  have HB : (|s 0| + 4 * c * ‖l 0‖ * J₀) * Real.exp (2 * J₀ + 8 * c * J₁) ≤ 5 := by
    have H := mul_le_mul Hfac Hexp (Real.exp_pos _).le (by norm_num : (0 : ℝ) ≤ 5 / 2)
    norm_num at H
    exact H
  have H := two_moment_variation_bound hT hs hl hb hb0 hds hdl
  intro t ht
  refine ⟨(H t ht).1.trans HB, (H t ht).2.trans ?_⟩
  have Hinner := mul_le_mul_of_nonneg_left HB (by positivity [ht.1] : 0 ≤ 2 * t)
  have Houter := mul_le_mul hc (add_le_add le_rfl Hinner)
    (by positivity [hJ₀, ht.1] : 0 ≤ ‖l 0‖ + 2 * t * ((|s 0| + 4 * c * ‖l 0‖ * J₀) * Real.exp (2 * J₀ + 8 * c * J₁)))
    (by norm_num : (0 : ℝ) ≤ 2)
  exact Houter.trans_eq (by ring)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_shearTailDrift {a : ℝ} (ha : a ≠ 0) (A X Y t : ℝ) :
    HasDerivAt (shearTailDrift a A X Y)
      (3 * Y ^ 2 * Real.exp (-a * t) + 3 * X ^ 2 * Real.exp (12 * a * t) +
        a * A / 4 * Real.exp (-2 * t)) t := by
  convert! (((((hasDerivAt_id' t).const_mul (-a)).exp.const_sub 1).const_mul (3 * Y ^ 2 / a)).add
    ((((hasDerivAt_id' t).const_mul (12 * a)).exp.sub_const 1).const_mul (X ^ 2 / (4 * a)))).add
      ((((hasDerivAt_id' t).const_mul (-2)).exp.const_sub 1).const_mul (a * A / 8)) using 1
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTailDrift_le {a A X Y T t : ℝ} (ha : 0 < a) (hA : 0 ≤ A) (ht : t ≤ T) :
    shearTailDrift a A X Y t ≤ 3 * Y ^ 2 / a +
      X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8 := by
  have HE := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ht (by positivity : 0 ≤ 12 * a))
  have HX := mul_le_mul_of_nonneg_left HE (by positivity : 0 ≤ X ^ 2 / (4 * a))
  have HY : 0 ≤ 3 * Y ^ 2 / a * Real.exp (-a * t) := by positivity
  have HN : 0 ≤ a * A / 8 * Real.exp (-2 * t) := by positivity
  dsimp only [shearTailDrift]
  nlinarith only [HX, HY, HN, show 0 ≤ X ^ 2 / (4 * a) by positivity]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.shearTail_prefix {a A X Y T : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, shearTailRegion a (α t))
    (hinit : α 0 2 ≤ A ∧ α 0 3 ≤ X ∧ α 0 4 ≤ Y) :
    ∀ t ∈ Icc (0 : ℝ) T,
      α t 2 ≤ A * Real.exp (-2 * t) ∧
      α t 3 ≤ X * Real.exp (6 * a * t) ∧
      α t 4 ≤ Y * Real.exp (-(a / 2) * t) ∧
      |α t 1 - α 0 1| ≤ shearTailDrift a A X Y t ∧
      a ^ 2 / 10 ≤ 1 + α t 0 ∧ 1 + α t 0 ≤ 6 * a ^ 2 ∧ α t 0 ≤ -(15 / 16) := by
  have H (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := hregion t ht
  have hp (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 < 0 := by linarith only [(H t ht).1]
  have HB (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    shearTail_constraint_bounds ha (hp t ht) ⟨(H t ht).2.1, (H t ht).2.2.1⟩
      ⟨(hn t ht).1, (H t ht).2.2.2.1⟩ ⟨(hn t ht).2.1, (H t ht).2.2.2.2.1⟩
      ⟨(hn t ht).2.2, (H t ht).2.2.2.2.2⟩ (hc t ht)
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :=
    shearTail_wall_rates ha (hp t ht) ⟨(H t ht).2.1, (H t ht).2.2.1⟩
      ⟨(hn t ht).1, (H t ht).2.2.2.1⟩ ⟨(hn t ht).2.1, (H t ht).2.2.2.2.1⟩
      ⟨(hn t ht).2.2, (H t ht).2.2.2.2.2⟩ (hc t ht)
  have HW (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      α t 2 ≤ A * Real.exp (-2 * t) ∧ α t 3 ≤ X * Real.exp (6 * a * t) ∧
        α t 4 ≤ Y * Real.exp (-(a / 2) * t) := by
    have hz : (0 : ℝ) ∈ Icc 0 T := ⟨le_rfl, ht.1.trans ht.2⟩
    have HD (u : ℝ) (hu : u ∈ Icc (0 : ℝ) T) := hasDerivAt_normalized_components (hα u hu)
    have Hn := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.1)
      (fun u hu => mul_le_mul_of_nonneg_right (HR u hu).1 (hn u hu).1) hz ht ht.1
    have Hx := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.2.1)
      (fun u hu => mul_le_mul_of_nonneg_right ((le_abs_self _).trans (HR u hu).2.1) (hn u hu).2.1) hz ht ht.1
    have Hy := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T)
      (fun u hu => (HD u hu).2.2.2.2)
      (fun u hu => mul_le_mul_of_nonneg_right (HR u hu).2.2 (hn u hu).2.2) hz ht ht.1
    simp only [sub_zero] at Hn Hx Hy
    rw [neg_div] at Hy
    exact ⟨Hn.trans (mul_le_mul_of_nonneg_right hinit.1 (Real.exp_pos _).le),
      Hx.trans (mul_le_mul_of_nonneg_right hinit.2.1 (Real.exp_pos _).le),
      Hy.trans (mul_le_mul_of_nonneg_right hinit.2.2 (Real.exp_pos _).le)⟩
  have HS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |shearMinus (α t 1) (α t 2) (α t 3) (α t 4)| ≤
        3 * Y ^ 2 * Real.exp (-a * t) + 3 * X ^ 2 * Real.exp (12 * a * t) +
          a * A / 4 * Real.exp (-2 * t) := by
    have Hs := shearTail_shear_rate ⟨ha.1.le, ha.2⟩
      (abs_le.mpr ⟨by linarith only [(H t ht).2.1, ha.1], (H t ht).2.2.1⟩)
      (hn t ht).1 (hn t ht).2.1 (hn t ht).2.2
    have Hx := pow_le_pow_left₀ (hn t ht).2.1 (HW t ht).2.1 2
    have Hy := pow_le_pow_left₀ (hn t ht).2.2 (HW t ht).2.2 2
    have hxsq : (X * Real.exp (6 * a * t)) ^ 2 = X ^ 2 * Real.exp (12 * a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    have hysq : (Y * Real.exp (-(a / 2) * t)) ^ 2 = Y ^ 2 * Real.exp (-a * t) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rw [hxsq] at Hx
    rw [hysq] at Hy
    have ha2 : a ^ 2 ≤ a / 256 := by nlinarith only [ha.1, ha.2]
    have hcoef : 3 * (α t 3 + α t 4 + a * α t 2) ≤ a / 4 := by
      have Han := mul_le_mul_of_nonneg_left (H t ht).2.2.2.1 ha.1.le
      have Haa := mul_le_mul_of_nonneg_left ha2 ha.1.le
      nlinarith only [Han, Haa, ha2, (H t ht).2.2.2.2.1, (H t ht).2.2.2.2.2]
    have Hcoef := mul_le_mul_of_nonneg_right hcoef (hn t ht).1
    have Hn := mul_le_mul_of_nonneg_left (HW t ht).1 (div_nonneg ha.1.le (by norm_num) : 0 ≤ a / 4)
    nlinarith only [Hs, Hx, Hy, Hcoef, Hn]
  have HG := abs_sub_le_of_deriv_primitive
    (fun t ht => (hasDerivAt_normalized_components (hα t ht)).2.1)
    (fun t _ => hasDerivAt_shearTailDrift ha.1.ne' A X Y t) HS
  intro t ht
  obtain ⟨Hn, Hx, Hy⟩ := HW t ht
  obtain ⟨_, _, _, _, Hp, Hl, Hu⟩ := HB t ht
  refine ⟨Hn, Hx, Hy, ?_, Hl, Hu, Hp⟩
  simpa only [shearTailDrift, mul_zero, Real.exp_zero, sub_self, mul_zero, zero_add, sub_zero] using HG t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isClosed_shearTailRegion (a : ℝ) : IsClosed {z | shearTailRegion a z} :=
  (isClosed_le (continuous_apply 0) continuous_const).inter
    ((isClosed_le continuous_const (continuous_apply 1)).inter
      ((isClosed_le (continuous_apply 1) continuous_const).inter
        ((isClosed_le (continuous_apply 2) continuous_const).inter
          ((isClosed_le (continuous_apply 3) continuous_const).inter
            (isClosed_le (continuous_apply 4) continuous_const)))))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalized_shearTail_control {a A X Y T : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hA : 0 ≤ A ∧ A < a ^ 2)
    (hX : 0 ≤ X ∧ X * Real.exp (6 * a * T) < a ^ 2)
    (hY : 0 ≤ Y ∧ Y < a / 16)
    (hc : stateConstraint z = 1) (hp : z 0 < 0)
    (hs : 3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hinit : z 2 ≤ A ∧ z 3 ≤ X ∧ z 4 ≤ Y) :
    ∀ t ∈ Icc (0 : ℝ) T,
      let w := normalizedMaxCurve z 0 t
      t ∈ normalizedMaxDomain z 0 ∧ shearTailRegion a w ∧
      w 2 ≤ A * Real.exp (-2 * t) ∧ w 3 ≤ X * Real.exp (6 * a * t) ∧
      w 4 ≤ Y * Real.exp (-(a / 2) * t) ∧ |w 1 - z 1| ≤ shearTailDrift a A X Y t ∧
      a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧ w 0 ≤ -(15 / 16) := by
  have hbudget : 3 * Y ^ 2 / a + X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8 ≤ a / 8 := by
    have HY := pow_le_pow_left₀ hY.1 hY.2.le 2
    have HX := pow_le_pow_left₀ (mul_nonneg hX.1 (Real.exp_pos _).le) hX.2.le 2
    have he : (X * Real.exp (6 * a * T)) ^ 2 = X ^ 2 * Real.exp (12 * a * T) := by
      rw [mul_pow, pow_two (Real.exp _), ← Real.exp_add]
      congr 2
      ring
    rw [he] at HX
    have HA := mul_le_mul_of_nonneg_left hA.2.le (sq_nonneg a)
    have haSq : a ^ 2 ≤ 1 / 256 := by nlinarith only [ha.1, ha.2]
    have Haa := mul_nonneg (sq_nonneg a) (sub_nonneg.mpr haSq)
    have hid : a * (3 * Y ^ 2 / a + X ^ 2 / (4 * a) * Real.exp (12 * a * T) + a * A / 8) =
        3 * Y ^ 2 + X ^ 2 * Real.exp (12 * a * T) / 4 + a ^ 2 * A / 8 := by
      field_simp [ha.1.ne']
    apply (mul_le_mul_iff_right₀ ha.1).mp
    rw [hid]
    nlinarith only [HY, HX, HA, Haa, sq_nonneg a]
  let α := normalizedMaxCurve z 0
  let S := {t : ℝ | shearTailRegion a (α t)}
  have hα (t : ℝ) (ht : 0 ≤ t) : HasDerivAt α (normalizedField (α t)) t :=
    (normalizedMaxCurve_forward_of_constraint hc ht).1
  have hcon (t : ℝ) (ht : 0 ≤ t) : stateConstraint (α t) = 1 :=
    (normalizedMaxCurve_forward_of_constraint hc ht).2.1
  have hnonneg (t : ℝ) (ht : 0 ≤ t) : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 :=
    ⟨(normalizedMaxCurve_wall_sign hc ht (0 : Fin 3)).2.mpr hn.1,
      (normalizedMaxCurve_wall_sign hc ht (1 : Fin 3)).2.mpr hn.2.1,
      (normalizedMaxCurve_wall_sign hc ht (2 : Fin 3)).2.mpr hn.2.2⟩
  have hzero : α 0 = z := normalizedMaxCurve_initial z 0
  have hXsmall : X < a ^ 2 := by
    have HE : 1 ≤ Real.exp (6 * a * T) := Real.one_le_exp_iff.mpr (by positivity [ha.1])
    exact (le_mul_of_one_le_right hX.1 HE).trans_lt hX.2
  have hsz : a / 2 ≤ z 1 ∧ z 1 ≤ 3 * a :=
    ⟨by linarith only [hs.1, ha.1], by linarith only [hs.2, ha.1]⟩
  have HB := shearTail_constraint_bounds ha hp hsz ⟨hn.1, hinit.1.trans hA.2.le⟩
    ⟨hn.2.1, hinit.2.1.trans hXsmall.le⟩ ⟨hn.2.2, hinit.2.2.trans hY.2.le⟩ hc
  have hS0 : (0 : ℝ) ∈ S := by
    change shearTailRegion a (α 0)
    rw [hzero]
    exact ⟨by linarith only [HB.2.2.2.2.1], hsz.1, hsz.2,
      hinit.1.trans hA.2.le, hinit.2.1.trans hXsmall.le, hinit.2.2.trans hY.2.le⟩
  have hclosed : IsClosed (S ∩ Icc 0 T) := by
    have H := (HasDerivAt.continuousOn (fun t (ht : t ∈ Icc (0 : ℝ) T) => hα t ht.1)).preimage_isClosed_of_isClosed
      isClosed_Icc (isClosed_shearTailRegion a)
    convert! H using 1
    ext t
    change (shearTailRegion a (α t) ∧ t ∈ Icc 0 T) ↔ (t ∈ Icc 0 T ∧ shearTailRegion a (α t))
    tauto
  have hwhole : Icc (0 : ℝ) T ⊆ S := by
    apply hclosed.Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hS0
    intro t ht hbefore
    obtain ⟨Hn, Hx, Hy, Hs, _, _, Hp⟩ := shearTail_prefix ha
      (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hnonneg u hu.1)
      (fun u hu => hbefore hu) (by simpa only [hzero] using hinit) t ⟨ht.1, le_rfl⟩
    have HD := Hs.trans ((shearTailDrift_le ha.1 hA.1 ht.2.le).trans hbudget)
    rw [hzero] at HD
    have Hsl : a / 2 < α t 1 := by linarith only [(abs_le.mp HD).1, hs.1, ha.1]
    have Hsu : α t 1 < 3 * a := by linarith only [(abs_le.mp HD).2, hs.2, ha.1]
    have Hnn : α t 2 < a ^ 2 := Hn.trans_lt
      ((mul_le_of_le_one_right hA.1 (Real.exp_le_one_iff.mpr (by linarith only [ht.1]))).trans_lt hA.2)
    have Hxx : α t 3 < a ^ 2 := Hx.trans_lt
      ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_left ht.2.le (by positivity [ha.1] : 0 ≤ 6 * a))) hX.1).trans_lt hX.2)
    have Hyy : α t 4 < a / 16 := Hy.trans_lt
      ((mul_le_of_le_one_right hY.1 (Real.exp_le_one_iff.mpr
        (mul_nonpos_of_nonpos_of_nonneg (by linarith only [ha.1] : -(a / 2) ≤ 0) ht.1))).trans_lt hY.2)
    have Hpp : α t 0 < -(1 / 2) := by linarith only [Hp]
    have Hcont (i : Fin 5) := (continuous_apply i).continuousAt.comp (hα t ht.1).continuousAt
    have Hev : ∀ᶠ u in 𝓝 t, u ∈ S := by
      filter_upwards [(Hcont 0).eventually (isOpen_Iio.mem_nhds Hpp),
        (Hcont 1).eventually (isOpen_Ioi.mem_nhds Hsl),
        (Hcont 1).eventually (isOpen_Iio.mem_nhds Hsu),
        (Hcont 2).eventually (isOpen_Iio.mem_nhds Hnn),
        (Hcont 3).eventually (isOpen_Iio.mem_nhds Hxx),
        (Hcont 4).eventually (isOpen_Iio.mem_nhds Hyy)] with u hu0 hu1 hu2 hu3 hu4 hu5
      exact ⟨hu0.le, hu1.le, hu2.le, hu3.le, hu4.le, hu5.le⟩
    exact Hev.filter_mono nhdsWithin_le_nhds
  have H := shearTail_prefix ha
    (fun u hu => hα u hu.1) (fun u hu => hcon u hu.1) (fun u hu => hnonneg u hu.1)
    (fun u hu => hwhole hu) (by simpa only [hzero] using hinit)
  intro t ht
  refine ⟨normalizedMaxDomain_contains_Ici_of_constraint hc 0 ht.1, hwhole ht, ?_⟩
  simpa only [hzero] using H t ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartSectionChart_constraint {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 ≤ restartSectionRadicand h Z) : stateConstraint (restartSectionChart h Z) = 1 := by
  have H := Real.sq_sqrt hZ
  dsimp [stateConstraint, constraint, shearSq, restartSectionChart]
  rw [neg_sq, H]
  unfold restartSectionRadicand
  ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearTail_prefix_moments {a T : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hT : 0 ≤ T)
    (hα : ∀ t ∈ Icc (0 : ℝ) T, HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) T, stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) T, 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hregion : ∀ t ∈ Icc (0 : ℝ) T, shearTailRegion a (α t)) :
    (∫ t in 0..T, shearTailEnergy (α t)) ≤
      (2 / 3 : ℝ) * (α 0 2 ^ 2 + α 0 2 * (α 0 3 + α 0 4)) + α 0 4 ^ 2 / a +
        α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * T) ∧
    (∫ t in 0..T, t * shearTailEnergy (α t)) ≤
      (4 / 9 : ℝ) * (α 0 2 ^ 2 + α 0 2 * (α 0 3 + α 0 4)) + α 0 4 ^ 2 / a ^ 2 +
        T * (α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * T)) := by
  let f : ℝ → ℝ := fun t => α t 2 ^ 2 + α t 2 * (α t 3 + α t 4)
  let r (i : Fin 3) (t : ℝ) : ℝ :=
    ![rateOne (α t 0) (α t 1), rateTwo (α t 0) (α t 1), rateThree (α t 0) (α t 1)] i
  have HR (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      r 0 t ≤ -2 ∧ r 1 t ≤ 6 * a ∧ r 2 t ≤ -a / 2 := by
    obtain ⟨hp, hsl, hsu, hN, hX, hY⟩ := hregion t ht
    have H := shearTail_wall_rates ha (by linarith only [hp]) ⟨hsl, hsu⟩
      ⟨(hn t ht).1, hN⟩ ⟨(hn t ht).2.1, hX⟩ ⟨(hn t ht).2.2, hY⟩ (hc t ht)
    exact ⟨H.1, (le_abs_self _).trans H.2.1, H.2.2⟩
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := hasDerivAt_normalized_components (hα t ht)
  have HF (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt f (2 * r 0 t * α t 2 ^ 2 + (r 0 t + r 1 t) * (α t 2 * α t 3) +
        (r 0 t + r 2 t) * (α t 2 * α t 4)) t := by
    convert! ((HD t ht).2.2.1.pow 2).add
      ((HD t ht).2.2.1.mul ((HD t ht).2.2.2.1.add (HD t ht).2.2.2.2)) using 1
    dsimp [r]
    ring
  have HFdec (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      2 * r 0 t * α t 2 ^ 2 + (r 0 t + r 1 t) * (α t 2 * α t 3) +
        (r 0 t + r 2 t) * (α t 2 * α t 4) ≤ -(3 / 2 : ℝ) * f t := by
    have H1 := mul_le_mul_of_nonneg_right (HR t ht).1 (sq_nonneg (α t 2))
    have H2 := mul_le_mul_of_nonneg_right
      (show r 0 t + r 1 t ≤ -(3 / 2 : ℝ) by linarith only [(HR t ht).1, (HR t ht).2.1, ha.2])
      (mul_nonneg (hn t ht).1 (hn t ht).2.1)
    have H3 := mul_le_mul_of_nonneg_right
      (show r 0 t + r 2 t ≤ -(3 / 2 : ℝ) by linarith only [(HR t ht).1, (HR t ht).2.2, ha.1])
      (mul_nonneg (hn t ht).1 (hn t ht).2.2)
    dsimp only [f]
    nlinarith only [H1, H2, H3, sq_nonneg (α t 2)]
  have HFM := integral_moments_le_of_linear_dissipation hT (by norm_num : (0 : ℝ) < 3 / 2)
    HF HFdec (by dsimp only [f]; positivity [(hn T ⟨hT, le_rfl⟩).1,
      (hn T ⟨hT, le_rfl⟩).2.1, (hn T ⟨hT, le_rfl⟩).2.2])
  have HYD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun t => α t 4 ^ 2) (2 * r 2 t * α t 4 ^ 2) t := by
    convert! (HD t ht).2.2.2.2.pow 2 using 1
    dsimp [r]
    ring
  have HYM := integral_moments_le_of_linear_dissipation hT ha.1 HYD (fun t ht => by
    have H := mul_le_mul_of_nonneg_right (HR t ht).2.2 (sq_nonneg (α t 4))
    nlinarith only [H]) (sq_nonneg (α T 4))
  have HXD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      HasDerivAt (fun t => α t 3 ^ 2) (2 * r 1 t * α t 3 ^ 2) t := by
    convert! (HD t ht).2.2.2.1.pow 2 using 1
    dsimp [r]
    ring
  have HX (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      α t 3 ^ 2 ≤ α 0 3 ^ 2 * Real.exp (12 * a * t) := by
    have H := le_exp_of_linear_deriv_le (convex_Icc (0 : ℝ) T) HXD (c := 12 * a)
      (fun u hu => by
        have H := mul_le_mul_of_nonneg_right (HR u hu).2.1 (sq_nonneg (α u 3))
        nlinarith only [H]) ⟨le_rfl, hT⟩ ht ht.1
    simpa only [sub_zero] using H
  have HGD (t : ℝ) : HasDerivAt (fun t => α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * t))
      (α 0 3 ^ 2 * Real.exp (12 * a * t)) t := by
    convert! (((hasDerivAt_id' t).const_mul (12 * a)).exp.const_mul (α 0 3 ^ 2 / (12 * a))) using 1
    field_simp [ha.1.ne']
  have hxcont := HasDerivAt.continuousOn HXD
  have hycont := HasDerivAt.continuousOn HYD
  have hfcont := HasDerivAt.continuousOn HF
  have hgcont : Continuous (fun t => α 0 3 ^ 2 * Real.exp (12 * a * t)) := by fun_prop
  have HXM : (∫ t in 0..T, α t 3 ^ 2) ≤ α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * T) := by
    have H := intervalIntegral.integral_mono_on (μ := volume) hT (hxcont.intervalIntegrable_of_Icc hT)
      (hgcont.intervalIntegrable _ _) HX
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => HGD t) (hgcont.intervalIntegrable _ _)] at H
    simp only [mul_zero, Real.exp_zero, mul_one] at H
    exact H.trans (sub_le_self _ (by positivity [ha.1]))
  have HXTM : (∫ t in 0..T, t * α t 3 ^ 2) ≤
      T * (α 0 3 ^ 2 / (12 * a) * Real.exp (12 * a * T)) := by
    have H := intervalIntegral.integral_mono_on (μ := volume) hT
      ((continuousOn_id.mul hxcont).intervalIntegrable_of_Icc hT)
      ((continuousOn_const.mul hxcont).intervalIntegrable_of_Icc hT)
      (fun t ht => mul_le_mul_of_nonneg_right ht.2 (sq_nonneg (α t 3)))
    simp only [Pi.mul_apply, id_eq] at H
    rw [intervalIntegral.integral_const_mul] at H
    exact H.trans (mul_le_mul_of_nonneg_left HXM hT)
  have he (t : ℝ) : shearTailEnergy (α t) = f t + α t 4 ^ 2 + α t 3 ^ 2 := by
    dsimp only [shearTailEnergy, f]
    ring
  simp only [sub_zero] at HFM HYM
  constructor
  · simp_rw [he]
    rw [intervalIntegral.integral_add (f := fun t => f t + α t 4 ^ 2) (g := fun t => α t 3 ^ 2)
      ((hfcont.add hycont).intervalIntegrable_of_Icc hT)
      (hxcont.intervalIntegrable_of_Icc hT),
      intervalIntegral.integral_add (hfcont.intervalIntegrable_of_Icc hT) (hycont.intervalIntegrable_of_Icc hT)]
    dsimp only [f] at HFM
    linarith only [HFM.1, HYM.1, HXM]
  · simp_rw [he, mul_add]
    rw [intervalIntegral.integral_add (f := fun t => t * f t + t * α t 4 ^ 2) (g := fun t => t * α t 3 ^ 2)
      (((continuousOn_id.mul hfcont).add (continuousOn_id.mul hycont)).intervalIntegrable_of_Icc hT)
      ((continuousOn_id.mul hxcont).intervalIntegrable_of_Icc hT),
      intervalIntegral.integral_add (f := fun t => t * f t) (g := fun t => t * α t 4 ^ 2)
        ((continuousOn_id.mul hfcont).intervalIntegrable_of_Icc hT)
        ((continuousOn_id.mul hycont).intervalIntegrable_of_Icc hT)]
    have Hsum := add_le_add (add_le_add HFM.2 HYM.2) HXTM
    dsimp only [f] at Hsum
    convert! Hsum using 1
    ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exp_shearTailTime {a : ℝ} (ha : 0 < a) (c D : ℝ) :
    Real.exp (c * a * shearTailTime a D) = a ^ (-c * D) := by
  rw [Real.rpow_def_of_pos ha]
  congr 1
  dsimp only [shearTailTime]
  rw [one_div, Real.log_inv]
  field_simp

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_shearTail_scale_control {h q D P : ℝ}
    (hh : 0 ≤ h) (hq : 2 < q) (hD : 0 ≤ D) (hP : 6 * D + 2 < P) :
    ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
      ∀ ε ζ : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) → (0 ≤ ζ ∧ ζ ≤ a ^ P) →
        ∀ z : NormalizedState, stateConstraint z = 1 → z 0 < 0 →
          (3 * a / 4 ≤ z 1 ∧ z 1 ≤ 9 * a / 4) →
          (0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4) →
          (z 2 ≤ h * a ^ q ∧ z 3 ≤ 2 * ζ ∧ z 4 ≤ 4 * ε * a) →
          let T := shearTailTime a D
          0 ≤ T ∧ ∀ t ∈ Icc (0 : ℝ) T,
            let w := normalizedMaxCurve z 0 t
            t ∈ normalizedMaxDomain z 0 ∧ shearTailRegion a w ∧
            w 2 ≤ h * a ^ q * Real.exp (-2 * t) ∧
            w 3 ≤ 2 * ζ * Real.exp (6 * a * t) ∧
            w 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * t) ∧
            |w 1 - z 1| ≤ 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 ∧
            a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧
            toProjectiveState w 2 < 1 := by
  let C : Fin 2 → ℝ := ![h, 40]
  let p : Fin 2 → ℝ := ![q - 2, P - 6 * D - 2]
  obtain ⟨astar, hastar, hastar', HB⟩ := exists_common_rpow_budget
    (C := C) (p := p) (ε := fun _ => (1 : ℝ) / 2) Finset.univ
    (fun i _ => by fin_cases i; exact hh; norm_num [C])
    (fun i _ => by fin_cases i; dsimp [p]; linarith only [hq]; dsimp [p]; linarith only [hP])
    (fun _ _ => by norm_num) (show (0 : ℝ) < 1 / 256 by norm_num)
  refine ⟨astar, hastar, ?_⟩
  intro a ha ε ζ hε hζ z hc hp hs hn hinit T
  have haSmall : a ≤ 1 / 256 := ha.2.trans hastar'.le
  have HN : h * a ^ (q - 2) < 1 / 2 := HB a ha 0 (Finset.mem_univ _)
  have HX : 40 * a ^ (P - 6 * D - 2) < 1 / 2 := HB a ha 1 (Finset.mem_univ _)
  have hR : 0 ≤ a ^ (P - 6 * D - 2) := Real.rpow_nonneg ha.1.le _
  have hNid : h * a ^ q = (h * a ^ (q - 2)) * a ^ 2 := by
    rw [Real.rpow_sub ha.1, Real.rpow_two]
    field_simp [ha.1.ne']
  have hXid : a ^ P * a ^ (-6 * D) = a ^ (P - 6 * D - 2) * a ^ 2 := by
    rw [← Real.rpow_two a, ← Real.rpow_add ha.1, ← Real.rpow_add ha.1]
    congr 1
    ring
  have hA : 0 ≤ h * a ^ q ∧ h * a ^ q < a ^ 2 := by
    refine ⟨mul_nonneg hh (Real.rpow_nonneg ha.1.le _), ?_⟩
    rw [hNid]
    have H := mul_lt_mul_of_pos_right HN (sq_pos_of_pos ha.1)
    nlinarith only [H, sq_pos_of_pos ha.1]
  have hXtotal : 2 * ζ * Real.exp (6 * a * T) < a ^ 2 / 40 := by
    change 2 * ζ * Real.exp (6 * a * shearTailTime a D) < _
    rw [exp_shearTailTime ha.1 6 D]
    have H := mul_le_mul_of_nonneg_right hζ.2 (Real.rpow_nonneg ha.1.le (-6 * D))
    rw [hXid] at H
    have H' := mul_lt_mul_of_pos_right HX (sq_pos_of_pos ha.1)
    nlinarith only [H, H']
  have hX : 0 ≤ 2 * ζ ∧ 2 * ζ * Real.exp (6 * a * T) < a ^ 2 :=
    ⟨by linarith only [hζ.1], hXtotal.trans (by nlinarith only [sq_pos_of_pos ha.1])⟩
  have hY : 0 ≤ 4 * ε * a ∧ 4 * ε * a < a / 16 := by
    have H := mul_le_mul_of_nonneg_right hε.2 ha.1.le
    exact ⟨mul_nonneg (by linarith only [hε.1]) ha.1.le, by linarith only [H, ha.1]⟩
  have hT : 0 ≤ T := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by linarith only [haSmall])))
  have H := normalized_shearTail_control ⟨ha.1, haSmall⟩ hT hA hX hY hc hp hs hn hinit
  refine ⟨hT, ?_⟩
  intro t ht w
  obtain ⟨Hdom, Hreg, Hn, Hx, Hy, Hs, HAl, HAu, _⟩ := H t ht
  have Hdrift := Hs.trans (shearTailDrift_le ha.1 hA.1 ht.2)
  have Hid : 3 * (4 * ε * a) ^ 2 / a + (2 * ζ) ^ 2 / (4 * a) * Real.exp (12 * a * T) +
      a * (h * a ^ q) / 8 = 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 := by
    change _ + _ * Real.exp (12 * a * shearTailTime a D) + _ = _
    rw [exp_shearTailTime ha.1 12 D, Real.rpow_add ha.1, Real.rpow_one]
    field_simp [ha.1.ne']
    ring
  refine ⟨Hdom, Hreg, Hn, Hx, Hy, Hdrift.trans_eq Hid, HAl, HAu, ?_⟩
  have hApos : 0 < 1 + w 0 := (div_pos (sq_pos_of_pos ha.1) (by norm_num)).trans_le HAl
  have hx0 : 0 ≤ w 3 := (normalizedMaxCurve_wall_sign hc ht.1 (1 : Fin 3)).2.mpr hn.2.1
  have hxsmall : w 3 < a ^ 2 / 40 := Hx.trans_lt
    ((mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr
      (mul_le_mul_of_nonneg_left ht.2 (by positivity [ha.1] : 0 ≤ 6 * a))) hX.1).trans_lt hXtotal)
  have hr : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  change Real.sqrt 3 * w 3 / (1 + w 0) < 1
  apply (div_lt_one hApos).mpr
  have Hr := mul_le_mul_of_nonneg_right hr hx0
  nlinarith only [Hr, hxsmall, HAl, sq_pos_of_pos ha.1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_polynomial_variation_bounds {z v : NormalizedState} {L : ℝ}
    (hL : 0 ≤ L) (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |curvature (z 2) (z 3) (z 4)| ≤ 2 * shearTailEnergy z ∧
    |shearTailCurvatureDifferential z v| ≤ 4 * shearTailEnergy z * L ∧
    |shearTailCouplingDifferential z v| ≤ 2 * shearTailEnergy z * L := by
  let M := z 2 + z 3 + z 4
  have hM : 0 ≤ M := by dsimp only [M]; positivity [hn.1, hn.2.1, hn.2.2]
  have hM2 : M ^ 2 ≤ 2 * shearTailEnergy z := by
    dsimp only [M, shearTailEnergy]
    nlinarith only [sq_nonneg (z 2), sq_nonneg (z 3 - z 4)]
  have hcoef : |z 2 - z 3 - z 4| ≤ M ∧ |z 3 - z 2 - z 4| ≤ M ∧ |z 4 - z 2 - z 3| ≤ M := by
    dsimp only [M]
    refine ⟨abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩, abs_le.mpr ⟨?_, ?_⟩⟩ <;>
      linarith only [hn.1, hn.2.1, hn.2.2]
  have HQraw : |shearTailCurvatureDifferential z v| ≤ 2 * M ^ 2 * L := by
    have H := abs_add_three ((z 2 - z 3 - z 4) * v 2) ((z 3 - z 2 - z 4) * v 3)
      ((z 4 - z 2 - z 3) * v 4)
    simp only [abs_mul] at H
    have Hn := mul_le_mul hcoef.1 hv.1 (abs_nonneg _) hM
    have Hx := mul_le_mul hcoef.2.1 hv.2.1 (abs_nonneg _) hM
    have Hy := mul_le_mul hcoef.2.2 hv.2.2 (abs_nonneg _) hM
    dsimp only [shearTailCurvatureDifferential]
    rw [abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num)]
    dsimp only [M] at Hn Hx Hy ⊢
    nlinarith only [H, Hn, Hx, Hy]
  refine ⟨(curvature_abs_le_sum_sq hn.1 hn.2.1 hn.2.2).trans hM2,
    HQraw.trans (by nlinarith only [mul_le_mul_of_nonneg_right hM2 hL]), ?_⟩
  have H := abs_add_three ((z 3 - z 4) * v 2) ((z 2 - 2 * z 3) * v 3) ((2 * z 4 - z 2) * v 4)
  simp only [abs_mul] at H
  have Hn := mul_le_mul (show |z 3 - z 4| ≤ z 3 + z 4 by
    exact abs_le.mpr ⟨by linarith only [hn.2.1], by linarith only [hn.2.2]⟩)
    hv.1 (abs_nonneg _) (add_nonneg hn.2.1 hn.2.2)
  have Hx := mul_le_mul (show |z 2 - 2 * z 3| ≤ z 2 + 2 * z 3 by
    exact abs_le.mpr ⟨by linarith only [hn.1], by linarith only [hn.2.1]⟩)
    hv.2.1 (abs_nonneg _) (by positivity [hn.1, hn.2.1] : 0 ≤ z 2 + 2 * z 3)
  have Hy := mul_le_mul (show |2 * z 4 - z 2| ≤ 2 * z 4 + z 2 by
    exact abs_le.mpr ⟨by linarith only [hn.2.2], by linarith only [hn.1]⟩)
    hv.2.2 (abs_nonneg _) (by positivity [hn.1, hn.2.2] : 0 ≤ 2 * z 4 + z 2)
  dsimp only [shearTailCouplingDifferential, shearTailEnergy]
  nlinarith only [H, Hn, Hx, Hy, mul_nonneg (sq_nonneg (z 2)) hL]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailVariationRate_bounds {z v : NormalizedState} {L : ℝ}
    (hp : z 0 ≤ -(15 / 16)) (hs : |z 1| ≤ 1 / 8)
    (hL : 0 ≤ L) (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hv : |v 2| ≤ z 2 * L ∧ |v 3| ≤ z 3 * L ∧ |v 4| ≤ z 4 * L) :
    |shearTailVariationRate z v 0| ≤ 2 * shearTailEnergy z * |v 1| + 4 * shearTailEnergy z * L ∧
    ∀ i : Fin 3, |shearTailVariationRate z v i.succ| ≤ 2 * |v 1| + 9 * shearTailEnergy z * L := by
  obtain ⟨HQ, HdQ, HdH⟩ := shearTail_polynomial_variation_bounds hL hn hv
  have hb : 0 ≤ shearTailEnergy z := by dsimp only [shearTailEnergy]; positivity [hn.1, hn.2.1, hn.2.2]
  have hξ : 0 < -z 0 := by linarith only [hp]
  have hi : 0 ≤ (-z 0)⁻¹ ∧ (-z 0)⁻¹ ≤ 5 / 4 := by
    refine ⟨inv_nonneg.mpr hξ.le, ?_⟩
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hξ).mpr
    linarith only [hp]
  have hr : |Real.sqrt (3 : ℝ)| ≤ 7 / 4 := by
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  have hsi : |z 1| * (-z 0)⁻¹ ≤ 1 / 4 := by
    have H := mul_le_mul hs hi.2 hi.1 (by norm_num : (0 : ℝ) ≤ 1 / 8)
    nlinarith only [H]
  have hc1 : |1 + (-z 0)⁻¹| ≤ 9 / 4 := by
    rw [abs_of_nonneg (by linarith only [hi.1] : 0 ≤ 1 + (-z 0)⁻¹)]
    linarith only [hi.2]
  have hc2 : |1 - (2 * (-z 0))⁻¹| ≤ 9 / 4 := by
    rw [mul_inv_rev]
    norm_num only [invOf_eq_inv, inv_eq_one_div]
    apply abs_le.mpr
    rw [← inv_eq_one_div] at *
    constructor <;> nlinarith only [hi.1, hi.2]
  have hs1 : |2 * z 1 * (-z 0)⁻¹| ≤ 2 := by
    rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < 2 by norm_num), abs_of_nonneg hi.1]
    nlinarith only [hsi]
  have hsp : |-z 1 * (-z 0)⁻¹ + Real.sqrt 3| ≤ 2 := by
    have H := abs_add_le (-z 1 * (-z 0)⁻¹) (Real.sqrt 3)
    rw [abs_mul, abs_neg, abs_of_nonneg hi.1] at H
    linarith only [H, hsi, hr]
  have hsm : |-z 1 * (-z 0)⁻¹ - Real.sqrt 3| ≤ 2 := by
    have H := abs_sub (-z 1 * (-z 0)⁻¹) (Real.sqrt 3)
    rw [abs_mul, abs_neg, abs_of_nonneg hi.1] at H
    linarith only [H, hsi, hr]
  have Hrow (A B : ℝ) (hA : |A| ≤ 9 / 4) (hB : |B| ≤ 2) :
      |A * shearTailCurvatureDifferential z v + B * v 1| ≤ 2 * |v 1| + 9 * shearTailEnergy z * L := by
    have H := abs_add_le (A * shearTailCurvatureDifferential z v) (B * v 1)
    rw [abs_mul, abs_mul] at H
    have HA := mul_le_mul hA HdQ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 9 / 4)
    have HB := mul_le_mul_of_nonneg_right hB (abs_nonneg (v 1))
    nlinarith only [H, HA, HB]
  constructor
  · have H := abs_add_three (curvature (z 2) (z 3) (z 4) * v 1)
      (z 1 * shearTailCurvatureDifferential z v) (Real.sqrt 3 * shearTailCouplingDifferential z v)
    simp only [abs_mul] at H
    have Hq := mul_le_mul_of_nonneg_right HQ (abs_nonneg (v 1))
    have Hs := mul_le_mul hs HdQ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1 / 8)
    have Hr := mul_le_mul hr HdH (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 7 / 4)
    change |curvature (z 2) (z 3) (z 4) * v 1 + z 1 * shearTailCurvatureDifferential z v +
      Real.sqrt 3 * shearTailCouplingDifferential z v| ≤ _
    nlinarith only [H, Hq, Hs, Hr]
  · intro i
    fin_cases i
    · exact Hrow _ _ hc1 hs1
    · exact Hrow _ _ hc2 hsp
    · exact Hrow _ _ hc2 hsm

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTailVariationRate_log_bounds {z v : NormalizedState}
    (hp : z 0 ≤ -(15 / 16)) (hs : |z 1| ≤ 1 / 8) (hn : positiveWalls z) :
    |shearTailVariationRate z v 0| ≤
      2 * shearTailEnergy z * |v 1| + 4 * shearTailEnergy z * shearTailLogSize z v ∧
    ∀ i : Fin 3, |shearTailVariationRate z v i.succ| ≤
      2 * |v 1| + 9 * shearTailEnergy z * shearTailLogSize z v := by
  have H (i : Fin 3) (hi : 0 < z (i.addNat 2)) :
      |v (i.addNat 2)| ≤ z (i.addNat 2) * shearTailLogSize z v := by
    have h := norm_le_pi_norm (fun j : Fin 3 => v (j.addNat 2) / z (j.addNat 2)) i
    rw [Real.norm_eq_abs, abs_div, abs_of_pos hi] at h
    have := (div_le_iff₀ hi).mp h
    simpa only [shearTailLogSize, mul_comm] using this
  exact shearTailVariationRate_bounds hp hs (norm_nonneg _)
    ⟨hn.1.le, hn.2.1.le, hn.2.2.le⟩ ⟨H 0 hn.1, H 1 hn.2.1, H 2 hn.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearTail_moment_bounds_linear {a D n x y : ℝ}
    (ha : 0 < a ∧ a ≤ 1) (hD : 0 ≤ D)
    (hn : 0 ≤ n ∧ n ≤ a ^ 2) (hx : 0 ≤ x ∧ x ≤ a ^ 2)
    (hy : 0 ≤ y ∧ y ≤ a / 16)
    (hX : x * Real.exp (6 * a * shearTailTime a D) ≤ a ^ 2) :
    (2 / 3 : ℝ) * (n ^ 2 + n * (x + y)) + y ^ 2 / a +
      x ^ 2 / (12 * a) * Real.exp (12 * a * shearTailTime a D) ≤ 4 * a ∧
    (4 / 9 : ℝ) * (n ^ 2 + n * (x + y)) + y ^ 2 / a ^ 2 +
      shearTailTime a D * (x ^ 2 / (12 * a) * Real.exp (12 * a * shearTailTime a D)) ≤
      1 / 256 + (2 + D) * a := by
  have ha2 : a ^ 2 ≤ a := by nlinarith only [ha.1, ha.2]
  have ha3 : a ^ 3 ≤ a := by
    have H := mul_le_mul_of_nonneg_left ha2 ha.1.le
    nlinarith only [H, ha2]
  have ha4 : a ^ 4 ≤ a ^ 3 := by
    have H := mul_le_mul_of_nonneg_right ha.2 (pow_nonneg ha.1.le 3)
    nlinarith only [H]
  have HF : n ^ 2 + n * (x + y) ≤ 3 * a ^ 3 := by
    have Hn := pow_le_pow_left₀ hn.1 hn.2 2
    have Hy : y ≤ a := hy.2.trans (by linarith only [ha.1])
    have Hxy := mul_le_mul hn.2 (add_le_add hx.2 Hy) (add_nonneg hx.1 hy.1) (sq_nonneg a)
    nlinarith only [Hn, Hxy, ha4]
  have HY := pow_le_pow_left₀ hy.1 hy.2 2
  have HY0 : y ^ 2 / a ≤ a / 256 := (div_le_iff₀ ha.1).mpr (by nlinarith only [HY])
  have HY1 : y ^ 2 / a ^ 2 ≤ 1 / 256 := (div_le_iff₀ (sq_pos_of_pos ha.1)).mpr (by nlinarith only [HY])
  have he : Real.exp (12 * a * shearTailTime a D) = Real.exp (6 * a * shearTailTime a D) ^ 2 := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  have HXsq := pow_le_pow_left₀ (mul_nonneg hx.1 (Real.exp_pos _).le) hX 2
  rw [mul_pow, ← he] at HXsq
  have HX0 : x ^ 2 / (12 * a) * Real.exp (12 * a * shearTailTime a D) ≤ a ^ 3 / 12 := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ (by positivity [ha.1] : 0 < 12 * a)).mpr
    nlinarith only [HXsq]
  have hlog : 0 ≤ Real.log (1 / a) := Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa using ha.2))
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le) hlog
  have halog : a * Real.log (1 / a) ≤ 1 := by
    have H := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (one_div_pos.mpr ha.1)) ha.1.le
    have heq : a * (1 / a - 1) = 1 - a := by field_simp [ha.1.ne']
    rw [heq] at H
    linarith only [H, ha.1]
  have HX1 : shearTailTime a D * (x ^ 2 / (12 * a) * Real.exp (12 * a * shearTailTime a D)) ≤ D * a := by
    apply (mul_le_mul_of_nonneg_left HX0 hT).trans
    have heq : shearTailTime a D * (a ^ 3 / 12) = (D * a / 12) * (a * Real.log (1 / a)) := by
      dsimp only [shearTailTime]
      field_simp [ha.1.ne']
    rw [heq]
    have H := mul_le_mul_of_nonneg_left halog (by positivity [ha.1] : 0 ≤ D * a / 12)
    nlinarith only [H, mul_nonneg hD ha.1.le]
  constructor
  · nlinarith only [HF, HY0, HX0, ha3, ha.1]
  · nlinarith only [HF, HY1, HX1, ha3, ha.1]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearTail_prefix_moments_linear {a D : ℝ} {α : ℝ → NormalizedState}
    (ha : 0 < a ∧ a ≤ 1 / 256) (hD : 0 ≤ D)
    (hα : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), HasDerivAt α (normalizedField (α t)) t)
    (hc : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), stateConstraint (α t) = 1)
    (hn : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4)
    (hr : ∀ t ∈ Icc (0 : ℝ) (shearTailTime a D), shearTailRegion a (α t))
    (hX : α 0 3 * Real.exp (6 * a * shearTailTime a D) ≤ a ^ 2) :
    (∫ t in 0..shearTailTime a D, shearTailEnergy (α t)) ≤ 4 * a ∧
    (∫ t in 0..shearTailTime a D, t * shearTailEnergy (α t)) ≤ 1 / 256 + (2 + D) * a := by
  have ha1 : a ≤ 1 := by linarith only [ha.2]
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa using ha1)))
  obtain ⟨_, _, _, hN, hX0, hY⟩ := hr 0 ⟨le_rfl, hT⟩
  have Hn := hn 0 ⟨le_rfl, hT⟩
  have H := shearTail_prefix_moments ha hT hα hc hn hr
  have HB := shearTail_moment_bounds_linear ⟨ha.1, ha1⟩ hD ⟨Hn.1, hN⟩ ⟨Hn.2.1, hX0⟩ ⟨Hn.2.2, hY⟩ hX
  exact ⟨H.1.trans HB.1, H.2.trans HB.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projectiveCoordinate_le {a p v B : ℝ}
    (ha : 0 < a) (hA : a ^ 2 / 10 ≤ 1 + p) (hv : 0 ≤ v ∧ v ≤ B) :
    0 ≤ projectiveCoord p v ∧ projectiveCoord p v ≤ 20 * B / a ^ 2 := by
  have hApos : 0 < 1 + p := (div_pos (sq_pos_of_pos ha) (by norm_num)).trans_le hA
  have hB : 0 ≤ B := hv.1.trans hv.2
  have hr : Real.sqrt (3 : ℝ) ≤ 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num), Real.sqrt_nonneg (3 : ℝ)]
  refine ⟨div_nonneg (mul_nonneg (Real.sqrt_nonneg _) hv.1) hApos.le, ?_⟩
  change Real.sqrt 3 * v / (1 + p) ≤ _
  calc
    _ ≤ 2 * B / (a ^ 2 / 10) := div_le_div₀ (by positivity : 0 ≤ 2 * B)
      (mul_le_mul hr hv.2 hv.1 (by norm_num)) (by positivity) hA
    _ = _ := by ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.shearTail_projective_endpoint {a h q D ε ζ : ℝ} {z : NormalizedState}
    (ha : 0 < a ∧ a ≤ 1) (hh : 0 ≤ h) (hD : 0 ≤ D)
    (hA : a ^ 2 / 10 ≤ 1 + z 0)
    (hn : 0 ≤ z 2 ∧ 0 ≤ z 3 ∧ 0 ≤ z 4)
    (hwall : z 2 ≤ h * a ^ q * Real.exp (-2 * shearTailTime a D) ∧
      z 3 ≤ 2 * ζ * Real.exp (6 * a * shearTailTime a D) ∧
      z 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * shearTailTime a D)) :
    0 ≤ toProjectiveState z 1 ∧ toProjectiveState z 1 ≤ 20 * h * a ^ (q - 2) ∧
    0 ≤ toProjectiveState z 2 ∧ toProjectiveState z 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧
    0 ≤ toProjectiveState z 3 ∧ toProjectiveState z 3 ≤ 80 * ε * a ^ (D / 2 - 1) := by
  have hT : 0 ≤ shearTailTime a D := mul_nonneg (div_nonneg hD ha.1.le)
    (Real.log_nonneg ((le_div_iff₀ ha.1).mpr (by simpa only [one_mul] using ha.2)))
  have Hn : z 2 ≤ h * a ^ q := hwall.1.trans
    (mul_le_of_le_one_right (mul_nonneg hh (Real.rpow_nonneg ha.1.le _))
      (Real.exp_le_one_iff.mpr (by linarith only [hT])))
  have Hx := hwall.2.1
  rw [exp_shearTailTime ha.1 6 D] at Hx
  have he : Real.exp (-(a / 2) * shearTailTime a D) = a ^ (D / 2) := by
    convert! exp_shearTailTime ha.1 (-(1 / 2)) D using 1 <;> congr 1 <;> ring
  have Hy := hwall.2.2
  rw [he] at Hy
  obtain ⟨Hn0, Hn1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.1, Hn⟩
  obtain ⟨Hx0, Hx1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.2.1, Hx⟩
  obtain ⟨Hy0, Hy1⟩ := shearTail_projectiveCoordinate_le ha.1 hA ⟨hn.2.2, Hy⟩
  refine ⟨Hn0, Hn1.trans_eq ?_, Hx0, Hx1.trans_eq ?_, Hy0, Hy1.trans_eq ?_⟩
  · rw [Real.rpow_sub ha.1, Real.rpow_two]
    ring
  · rw [Real.rpow_sub ha.1, Real.rpow_two]
    ring
  · rw [Real.rpow_sub ha.1, Real.rpow_one]
    field_simp [ha.1.ne']
    ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.shearTailLogSize_eq_norm_variation (z v : NormalizedState) :
    shearTailLogSize z v = ‖fun i : Fin 3 => shearTailVariation z v i.succ‖ := by
  congr 1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_restartSectionChart {h : ℝ} {Z : RestartCenterState}
    (hZ : 0 < restartSectionRadicand h Z) (k : WithTop ℕ∞) :
    ContDiffAt ℝ k (restartSectionChart h) Z := by
  have hr : ContDiff ℝ k (restartSectionRadicand h) := by
    unfold restartSectionRadicand curvature
    fun_prop
  rw [contDiffAt_pi]
  intro i
  fin_cases i
  · exact (hr.contDiffAt.sqrt hZ.ne').neg
  · exact contDiffAt_apply ℝ ℝ (0 : Fin 3) Z
  · exact contDiffAt_const
  · exact contDiffAt_apply ℝ ℝ (1 : Fin 3) Z
  · exact contDiffAt_apply ℝ ℝ (2 : Fin 3) Z

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.hasDerivAt_restartShearCurve (σ n₂ n₃ ρ : ℝ) :
    HasDerivAt (restartShearCurve σ n₂ n₃) (restartShearDirection σ) ρ := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · simpa [restartShearCurve, restartShearDirection] using (hasDerivAt_id ρ).const_mul σ
  · convert! hasDerivAt_const ρ n₂ using 1
  · convert! hasDerivAt_const ρ n₃ using 1

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_restartShearTail_control :
    ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 ≤ ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 ≤ ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let Z := restartShearCurve 1 ζ ν ρ
            let t₀ := q / 2 * Real.log (1 / a)
            let T := shearTailTime a D
            let x := restartSectionChart h Z
            let y := normalizedMaxCurve x 0 t₀
            a ≤ 1 ∧ 0 ≤ t₀ ∧ 0 ≤ T ∧ 0 < restartSectionRadicand h Z ∧ stateConstraint x = 1 ∧
            (∀ t ∈ Icc (0 : ℝ) T,
              let w := restartShearTailFlow h a q ζ ν t ρ
              t + t₀ ∈ normalizedMaxDomain x 0 ∧ w = normalizedMaxCurve y 0 t ∧
              stateConstraint w = 1 ∧ (0 ≤ w 2 ∧ 0 ≤ w 3 ∧ 0 ≤ w 4) ∧
              shearTailRegion a w ∧ w 2 ≤ h * a ^ q * Real.exp (-2 * t) ∧
              w 3 ≤ 2 * ζ * Real.exp (6 * a * t) ∧
              w 4 ≤ 4 * ε * a * Real.exp (-(a / 2) * t) ∧
              |w 1 - y 1| ≤ 48 * ε ^ 2 * a + ζ ^ 2 / a * a ^ (-12 * D) + h * a ^ (q + 1) / 8 ∧
              a ^ 2 / 10 ≤ 1 + w 0 ∧ 1 + w 0 ≤ 6 * a ^ 2 ∧ toProjectiveState w 2 < 1) ∧
            (let w := restartShearTailFlow h a q ζ ν T ρ;
              toProjectiveState w 1 ≤ 20 * h * a ^ (q - 2) ∧
              toProjectiveState w 2 ≤ 40 * ζ * a ^ (-6 * D - 2) ∧
              toProjectiveState w 3 ≤ 80 * ε * a ^ (D / 2 - 1)) := by
  obtain ⟨C, _, hstar, hhstar, HF⟩ := exists_restartShearFastEntry_control
  refine ⟨hstar, hhstar, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aF, haF, HFa⟩ := HF h hh q hq
  obtain ⟨aT, haT, HTa⟩ := exists_shearTail_scale_control hh.1.le hq hD hP
  refine ⟨min aF aT, lt_min haF haT, ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ Z t₀ T x y
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, by linarith only [hε.2]⟩
  obtain ⟨ha1, _, ht₀, hrad, hdom, hcy, hpy, _, hnpos, hnhi, hsy, _, _, _, HW⟩ :=
    HFa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩ ε 1 ζ ν hε' (by norm_num)
      ⟨hζ.1, hζ.2.2⟩ hν ρ hρ
  have hcx : stateConstraint x = 1 := restartSectionChart_constraint hrad.le
  have Hn : 0 ≤ y 2 ∧ y 2 ≤ h * a ^ q := ⟨hnpos.le, hnhi⟩
  have Hx : 0 ≤ y 3 ∧ y 3 ≤ 2 * ζ := by
    have H := HW 0
    change ζ / 2 ≤ y 3 ∧ y 3 ≤ 2 * ζ ∧ _ at H
    exact ⟨by linarith only [H.1, hζ.1], H.2.1⟩
  have Hy : 0 ≤ y 4 ∧ y 4 ≤ 4 * ε * a := by
    have H := HW 1
    change ν / 2 ≤ y 4 ∧ y 4 ≤ 2 * ν ∧ _ at H
    exact ⟨by linarith only [H.1, hν.1], by linarith only [H.2.1, hν.2]⟩
  have HS : 3 * a / 4 ≤ y 1 ∧ y 1 ≤ 9 * a / 4 := by
    change 3 * a / 4 ≤ 1 * y 1 ∧ 1 * y 1 ≤ 9 * a / 4 at hsy
    simpa only [one_mul] using hsy
  obtain ⟨hT, HT⟩ := HTa a ⟨ha.1, ha.2.trans (min_le_right _ _)⟩ ε ζ hε
    ⟨hζ.1, hζ.2.1⟩ y hcy (by linarith only [hpy]) HS ⟨Hn.1, Hx.1, Hy.1⟩ ⟨Hn.2, Hx.2, Hy.2⟩
  have Hall (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      t + t₀ ∈ normalizedMaxDomain x 0 ∧
      restartShearTailFlow h a q ζ ν t ρ = normalizedMaxCurve y 0 t ∧
      stateConstraint (restartShearTailFlow h a q ζ ν t ρ) = 1 ∧
      (0 ≤ restartShearTailFlow h a q ζ ν t ρ 2 ∧
        0 ≤ restartShearTailFlow h a q ζ ν t ρ 3 ∧ 0 ≤ restartShearTailFlow h a q ζ ν t ρ 4) := by
    have htime : 0 ≤ t + t₀ := add_nonneg ht.1 ht₀
    have htot := normalizedMaxDomain_contains_Ici_of_constraint hcx 0 htime
    have Heq : restartShearTailFlow h a q ζ ν t ρ = normalizedMaxCurve y 0 t := by
      change normalizedMaxCurve x 0 (t + t₀) = normalizedMaxCurve (normalizedMaxCurve x 0 t₀) 0 t
      simpa only [zero_add] using
        (normalizedMaxCurve_shift (by simpa only [zero_add] using hdom) htot).symm
    refine ⟨htot, Heq, (normalizedMaxCurve_forward_of_constraint hcx htime).2.1, ?_⟩
    rw [Heq]
    exact ⟨(normalizedMaxCurve_wall_sign hcy ht.1 (0 : Fin 3)).2.mpr Hn.1,
      (normalizedMaxCurve_wall_sign hcy ht.1 (1 : Fin 3)).2.mpr Hx.1,
      (normalizedMaxCurve_wall_sign hcy ht.1 (2 : Fin 3)).2.mpr Hy.1⟩
  refine ⟨ha1, ht₀, hT, hrad, hcx, ?_, ?_⟩
  · intro t ht w
    obtain ⟨Hdom, Heq, Hc, Hpos⟩ := Hall t ht
    refine ⟨Hdom, Heq, Hc, Hpos, ?_⟩
    change w = normalizedMaxCurve y 0 t at Heq
    rw [Heq]
    exact (HT t ht).2
  · have heq := (Hall T ⟨hT, le_rfl⟩).2.1
    obtain ⟨_, _, HnT, HxT, HyT, _, HAl, _, _⟩ := HT T ⟨hT, le_rfl⟩
    have Hpos := (Hall T ⟨hT, le_rfl⟩).2.2.2
    rw [heq] at Hpos ⊢
    have Hproj := shearTail_projective_endpoint ⟨ha.1, ha1⟩ hh.1.le hD HAl Hpos ⟨HnT, HxT, HyT⟩
    exact ⟨Hproj.2.1, Hproj.2.2.2.1, Hproj.2.2.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartShearInitialVariation_tangent {h ζ ν ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ)) :
    HasDerivAt (fun r => restartSectionChart h (restartShearCurve 1 ζ ν r))
      (restartShearInitialVariation h ζ ν ρ) ρ ∧
    normalizedConstraintDifferential (restartSectionChart h (restartShearCurve 1 ζ ν ρ))
      (restartShearInitialVariation h ζ ν ρ) = 0 := by
  have HD := ((contDiffAt_restartSectionChart hrad 1).differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    ρ (hasDerivAt_restartShearCurve 1 ζ ν ρ)
  refine ⟨HD, ?_⟩
  have HR : Continuous (fun r => restartSectionRadicand h (restartShearCurve 1 ζ ν r)) := by
    unfold restartSectionRadicand restartShearCurve curvature
    fun_prop
  have HE : (fun r => stateConstraint (restartSectionChart h (restartShearCurve 1 ζ ν r))) =ᶠ[𝓝 ρ]
      fun _ => (1 : ℝ) := by
    filter_upwards [HR.continuousAt.eventually (isOpen_Ioi.mem_nhds hrad)] with r hr
    exact restartSectionChart_constraint hr.le
  exact ((hasFDerivAt_stateConstraint _).comp_hasDerivAt ρ HD).unique
    ((hasDerivAt_const ρ (1 : ℝ)).congr_of_eventuallyEq HE)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_restartShearTailFlow {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0) :
    HasDerivAt (restartShearTailFlow h a q ζ ν t) (restartShearTailRadialVariation h a q ζ ν t ρ) ρ := by
  exact (hasFDerivAt_normalizedMaxCurve_initial ht).comp_hasDerivAt ρ
    (restartShearInitialVariation_tangent hrad).1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.restartShearTail_radial_equation {h a q ζ ν t ρ : ℝ}
    (hrad : 0 < restartSectionRadicand h (restartShearCurve 1 ζ ν ρ))
    (ht : t + q / 2 * Real.log (1 / a) ∈
      normalizedMaxDomain (restartSectionChart h (restartShearCurve 1 ζ ν ρ)) 0)
    (hp : restartShearTailFlow h a q ζ ν t ρ 0 ≤ -(15 / 16))
    (hs : |restartShearTailFlow h a q ζ ν t ρ 1| ≤ 1 / 8)
    (hn : positiveWalls (restartShearTailFlow h a q ζ ν t ρ)) :
    let z := restartShearTailFlow h a q ζ ν t ρ
    let v := restartShearTailRadialVariation h a q ζ ν t ρ
    HasDerivAt (fun u => shearTailVariation (restartShearTailFlow h a q ζ ν u ρ)
      (restartShearTailRadialVariation h a q ζ ν u ρ)) (shearTailVariationRate z v) t ∧
    |shearTailVariationRate z v 0| ≤ 2 * shearTailEnergy z * |v 1| +
      4 * shearTailEnergy z * shearTailLogSize z v ∧
    ∀ i : Fin 3, |shearTailVariationRate z v i.succ| ≤ 2 * |v 1| +
      9 * shearTailEnergy z * shearTailLogSize z v := by
  intro z v
  refine ⟨?_, shearTailVariationRate_log_bounds hp hs hn⟩
  have H := normalizedFlow_shearTailVariation ht (restartShearInitialVariation_tangent hrad).2
    (by change z 0 ≠ 0; linarith only [hp]) hn.1.ne' hn.2.1.ne' hn.2.2.ne'
  have Ht := H.scomp t ((hasDerivAt_id' t).add_const (q / 2 * Real.log (1 / a)))
  simpa only [Function.comp_def, one_smul, restartShearTailFlow, restartShearTailRadialVariation, z, v] using Ht

end
end

/-- One scale proves all moment budgets and the actual radial bounds throughout the joined tail. -/
theorem solution :
    ∃ C ≥ (32 : ℝ), ∃ hstar > (0 : ℝ), ∀ h ∈ Ioc (0 : ℝ) hstar,
      ∀ q D P : ℝ, 2 < q → 0 ≤ D → 6 * D + 2 < P →
        ∃ astar > (0 : ℝ), ∀ a ∈ Ioc (0 : ℝ) astar,
          ∀ ε ζ ν : ℝ, (0 ≤ ε ∧ ε ≤ 1 / 128) →
            (0 < ζ ∧ ζ ≤ a ^ P ∧ ζ ≤ 2 * ε * a) →
            (0 < ν ∧ ν ≤ 2 * ε * a) → ∀ ρ ∈ Icc a (2 * a),
            let T := shearTailTime a D
            let α := fun t => restartShearTailFlow h a q ζ ν t ρ
            let v := fun t => restartShearTailRadialVariation h a q ζ ν t ρ
            let L₀ := shearTailLogSize (α 0) (v 0)
            let J₀ := ∫ t in 0..T, shearTailEnergy (α t)
            let J₁ := ∫ t in 0..T, t * shearTailEnergy (α t)
            a ≤ 1 / 256 ∧ 0 ≤ T ∧ L₀ ≤ 2 + 4 * C * q * |Real.log a| ∧
            J₀ ≤ 4 * a ∧ J₁ ≤ 1 / 256 + (2 + D) * a ∧
            9 * J₀ ≤ Real.log 2 ∧ 2 * J₀ + 16 * J₁ ≤ 1 / 2 ∧ L₀ * J₀ ≤ 1 / 16 ∧
            ∀ t ∈ Icc (0 : ℝ) T,
              HasDerivAt (restartShearTailFlow h a q ζ ν t) (v t) ρ ∧ positiveWalls (α t) ∧
              |v t 1| ≤ 5 ∧ shearTailLogSize (α t) (v t) ≤ 2 * L₀ + 20 * t ∧
              shearTailLogSize (α t) (v t) ≤ 4 + 8 * C * q * |Real.log a| + 20 * t := by
  obtain ⟨hV, hhV, HV⟩ := exists_restartShearTail_control
  obtain ⟨C, hC, hI, hhI, HI⟩ := exists_restartShearTail_initial_variation
  refine ⟨C, hC, min hV hI, lt_min hhV hhI, ?_⟩
  intro h hh q D P hq hD hP
  obtain ⟨aV, haV, HVa⟩ := HV h ⟨hh.1, hh.2.trans (min_le_left _ _)⟩ q D P hq hD hP
  obtain ⟨aI, haI, HIa⟩ := HI h ⟨hh.1, hh.2.trans (min_le_right _ _)⟩ q hq
  obtain ⟨aB, haB, HBa⟩ := exists_shearTail_variation_budget
    (le_trans (by norm_num : (0 : ℝ) ≤ 32) hC) hq hP
  refine ⟨min aV (min aI aB), lt_min haV (lt_min haI haB), ?_⟩
  intro a ha ε ζ ν hε hζ hν ρ hρ T α v L₀ J₀ J₁
  let t₀ := q / 2 * Real.log (1 / a)
  let x := restartSectionChart h (restartShearCurve 1 ζ ν ρ)
  obtain ⟨_, ht₀, hT, hrad, hcx, HT, _⟩ := HVa a ⟨ha.1, ha.2.trans (min_le_left _ _)⟩
    ε ζ ν hε ⟨hζ.1.le, hζ.2⟩ ⟨hν.1.le, hν.2⟩ ρ hρ
  have hε' : 0 ≤ ε ∧ ε ≤ 1 / 64 := ⟨hε.1, by linarith only [hε.2]⟩
  obtain ⟨_, _, _, _, Hs₀, HL₀⟩ := HIa a
    ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_left _ _))⟩ ε ζ ν hε'
    ⟨hζ.1, hζ.2.2⟩ hν ρ hρ
  obtain ⟨hasmall, hpow, HB⟩ := HBa a ⟨ha.1, ha.2.trans ((min_le_right _ _).trans (min_le_right _ _))⟩
  have Hdom (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : t + t₀ ∈ normalizedMaxDomain x 0 := (HT t ht).1
  have Hcon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : stateConstraint (α t) = 1 := (HT t ht).2.2.1
  have Hnon (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ α t 2 ∧ 0 ≤ α t 3 ∧ 0 ≤ α t 4 := (HT t ht).2.2.2.1
  have Hreg (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : shearTailRegion a (α t) := (HT t ht).2.2.2.2.1
  have Hpos (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : positiveWalls (α t) :=
    (normalizedMaxCurve_forward (show positiveWalls x from ⟨hh.1, hζ.1, hν.1⟩) hcx
      (add_nonneg ht.1 ht₀)).2.1
  have HD (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt α (normalizedField (α t)) t := by
    have H := (hasDerivAt_normalizedMaxCurve (Hdom t ht)).scomp t ((hasDerivAt_id' t).add_const t₀)
    simpa only [Function.comp_def, one_smul, α, restartShearTailFlow, x, t₀] using H
  have Hgrow : α 0 3 * Real.exp (6 * a * T) ≤ a ^ 2 := by
    obtain ⟨_, _, _, _, _, _, Hx, _⟩ := HT 0 ⟨le_rfl, hT⟩
    simp only [mul_zero, Real.exp_zero, mul_one] at Hx
    change α 0 3 ≤ 2 * ζ at Hx
    change α 0 3 * Real.exp (6 * a * shearTailTime a D) ≤ a ^ 2
    rw [exp_shearTailTime ha.1 6 D]
    have Hid : a ^ P * a ^ (-6 * D) = a ^ (P - 6 * D - 2) * a ^ 2 := by
      rw [← Real.rpow_two a, ← Real.rpow_add ha.1, ← Real.rpow_add ha.1]
      congr 1
      ring
    calc
      _ ≤ (2 * a ^ P) * a ^ (-6 * D) := mul_le_mul_of_nonneg_right
        (Hx.trans (mul_le_mul_of_nonneg_left hζ.2.1 (by norm_num))) (Real.rpow_nonneg ha.1.le _)
      _ = (2 * a ^ (P - 6 * D - 2)) * a ^ 2 := by rw [mul_assoc, Hid]; ring
      _ ≤ a ^ 2 := by simpa only [one_mul] using mul_le_mul_of_nonneg_right hpow (sq_nonneg a)
  have HM := shearTail_prefix_moments_linear ⟨ha.1, hasmall⟩ hD HD Hcon Hnon Hreg Hgrow
  have Hb0 (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : 0 ≤ shearTailEnergy (α t) := by
    dsimp only [shearTailEnergy]
    positivity [(Hnon t ht).1, (Hnon t ht).2.1, (Hnon t ht).2.2]
  have HJ₀ : 0 ≤ J₀ := intervalIntegral.integral_nonneg hT Hb0
  obtain ⟨HB0, HB1, HBL⟩ := HB L₀ J₀ J₁ HL₀ HJ₀ HM.1 HM.2
  have Hregion (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : α t 0 ≤ -(15 / 16) ∧ |α t 1| ≤ 1 / 8 := by
    obtain ⟨hp, hsl, hsu, hn, hx, hy⟩ := Hreg t ht
    obtain ⟨_, _, _, _, Hpp, _, _⟩ := shearTail_constraint_bounds ⟨ha.1, hasmall⟩
      (by linarith only [hp]) ⟨hsl, hsu⟩ ⟨(Hnon t ht).1, hn⟩ ⟨(Hnon t ht).2.1, hx⟩
      ⟨(Hnon t ht).2.2, hy⟩ (Hcon t ht)
    exact ⟨Hpp, abs_le.mpr ⟨by linarith only [hsl, ha.1], by linarith only [hsu, hasmall]⟩⟩
  have HVeq (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) := restartShearTail_radial_equation hrad
    (Hdom t ht) (Hregion t ht).1 (Hregion t ht).2 (Hpos t ht)
  let S : ℝ → ℝ := fun t => v t 1
  let L : ℝ → (Fin 3 → ℝ) := fun t i => shearTailVariation (α t) (v t) i.succ
  let S' : ℝ → ℝ := fun t => shearTailVariationRate (α t) (v t) 0
  let L' : ℝ → (Fin 3 → ℝ) := fun t i => shearTailVariationRate (α t) (v t) i.succ
  have HE (t : ℝ) : shearTailLogSize (α t) (v t) = ‖L t‖ := shearTailLogSize_eq_norm_variation _ _
  have HS (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt S (S' t) t := hasDerivAt_pi.mp (HVeq t ht).1 0
  have HL (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) : HasDerivAt L (L' t) t :=
    hasDerivAt_pi.mpr (fun i => hasDerivAt_pi.mp (HVeq t ht).1 i.succ)
  have Hα := HasDerivAt.continuousOn HD
  have Hb : ContinuousOn (fun t => shearTailEnergy (α t)) (Icc (0 : ℝ) T) := by unfold shearTailEnergy; fun_prop
  have HSb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      |S' t| ≤ 2 * shearTailEnergy (α t) * |S t| + 4 * shearTailEnergy (α t) * ‖L t‖ := by
    simpa only [← HE t] using (HVeq t ht).2.1
  have HLb (t : ℝ) (ht : t ∈ Icc (0 : ℝ) T) :
      ‖L' t‖ ≤ 2 * |S t| + 9 * shearTailEnergy (α t) * ‖L t‖ := by
    apply (pi_norm_le_iff_of_nonneg (by positivity [Hb0 t ht])).mpr
    intro i
    simpa only [Real.norm_eq_abs, ← HE t] using (HVeq t ht).2.2 i
  have Hvariation := two_moment_variation_small hT HS HL Hb Hb0 HSb HLb Hs₀
    ⟨HB0, HB1, by simpa only [← HE 0] using HBL⟩
  refine ⟨hasmall, hT, HL₀, HM.1, HM.2, HB0, HB1, HBL, ?_⟩
  intro t ht
  have Hlog : shearTailLogSize (α t) (v t) ≤ 2 * L₀ + 20 * t := by
    simpa only [← HE] using (Hvariation t ht).2
  exact ⟨hasDerivAt_restartShearTailFlow hrad (Hdom t ht), Hpos t ht,
    (Hvariation t ht).1, Hlog, by linarith only [Hlog, HL₀]⟩
