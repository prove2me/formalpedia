-- Prove2me | solution 1 for BianchiIX.exists_stableCorrectedRemainder_amplitude_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:51:12.045047+00:00
-- url     : https://prove2.me/submissions/07674627-060b-4926-8ad1-faf003cee5c6

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_Dynamics_WallEvolution
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_stableBoundaryProjection_two_in_band
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_stableRescaledResidualRate_weighted_decay
import Theorems.Thm_BianchiIX_exists_stableResidual_derivative_integral_tails
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_normalizedMaxCurve_wall_sign
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_normalized_stable_global_region
import Theorems.Thm_BianchiIX_normalized_stable_limit
import Theorems.Thm_BianchiIX_reciprocalProfile_derivative_bounds
import Theorems.Thm_BianchiIX_stableScaledResidualCubic_bounds_of_coefficients
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.MetricSpace.Cauchy
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Topology.Order.Compact
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open BianchiIX

section
noncomputable section
open BianchiIX
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_fderiv_apply_const {f : E → F} {gamma : ℝ → E} {v : E} {t : ℝ}
    (hf : DifferentiableAt ℝ (fderiv ℝ f) (gamma t))
    (hg : HasDerivAt gamma v t) (w : E) :
    HasDerivAt (fun s => fderiv ℝ f (gamma s) w)
      (fderiv ℝ (fderiv ℝ f) (gamma t) v w) t := by
  have H := (hf.hasFDerivAt.comp_hasDerivAt t hg).clm_apply (hasDerivAt_const t w)
  simpa only [Function.comp_apply, ContinuousLinearMap.map_zero, add_zero] using H

end
end

section
noncomputable section
open BianchiIX
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.contDiffAt_partial_fderiv {f : E × F → G} {x : E} {y : F} {m n : WithTop ℕ∞}
    (hf : ContDiffAt ℝ n f (x, y)) (hmn : m + 1 ≤ n) :
    ContDiffAt ℝ m (fun p : E × F => fderiv ℝ (fun z => f (p.1, z)) p.2) (x, y) := by
  have hp : ContDiffAt ℝ n (fun p : (E × F) × F => (p.1.1, p.2)) ((x, y), y) :=
    contDiffAt_fst.fst.prodMk contDiffAt_snd
  have H : ContDiffAt ℝ n
      (Function.uncurry (fun p : E × F => fun z : F => f (p.1, z))) ((x, y), y) :=
    hf.comp ((x, y), y) hp
  exact H.fderiv contDiffAt_snd hmn

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.fderiv2_comp_apply {f : E → F} {g : F → G} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g (f x)) (v w : E) :
    fderiv ℝ (fderiv ℝ (g ∘ f)) x v w =
      fderiv ℝ g (f x) (fderiv ℝ (fderiv ℝ f) x v w) +
        fderiv ℝ (fderiv ℝ g) (f x) (fderiv ℝ f x v) (fderiv ℝ f x w) := by
  have hf' := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hg' := (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hcomp := ((hg.comp x hf).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (g ∘ f) y w) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ g (f y) (fderiv ℝ f y w)) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually (hg.eventually (by norm_num))]
      with y hfy hgy
    rw [fderiv_comp y (hgy.differentiableAt (by norm_num)) (hfy.differentiableAt (by norm_num))]
    rfl
  have Hleft := hcomp.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have Hright := (hg'.hasFDerivAt.comp x (hf.differentiableAt (by norm_num)).hasFDerivAt).clm_apply
    (hf'.hasFDerivAt.clm_apply (hasFDerivAt_const w x))
  have H := congrArg (fun L : E →L[ℝ] G => L v) (Hleft.unique (Hright.congr_of_eventuallyEq heq))
  simpa using H

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup G] [NormedSpace ℝ G]

private theorem BianchiIX.fderiv2_mul_apply {f g : E → ℝ} {x : E}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x v w =
      f x * fderiv ℝ (fderiv ℝ g) x v w +
        fderiv ℝ f x v * fderiv ℝ g x w +
        fderiv ℝ f x w * fderiv ℝ g x v +
        fderiv ℝ (fderiv ℝ f) x v w * g x := by
  have hf' := (hf.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hg' := (hg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have hp := ((hf.mul hg).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiableAt (by norm_num)
  have heq : (fun y => fderiv ℝ (fun z => f z * g z) y w) =ᶠ[𝓝 x]
      (fun y => f y * fderiv ℝ g y w + fderiv ℝ f y w * g y) := by
    filter_upwards [hf.eventually (by norm_num), hg.eventually (by norm_num)] with y hfy hgy
    rw [fderiv_fun_mul (hfy.differentiableAt (by norm_num)) (hgy.differentiableAt (by norm_num))]
    simp
    ring
  have Hleft := hp.hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  have Hright := ((hf.differentiableAt (by norm_num)).hasFDerivAt.mul
    (hg'.hasFDerivAt.clm_apply (hasFDerivAt_const w x))).add
    ((hf'.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).mul (hg.differentiableAt (by norm_num)).hasFDerivAt)
  have H := congrArg (fun L : E →L[ℝ] ℝ => L v) (Hleft.unique (Hright.congr_of_eventuallyEq heq))
  simpa [add_assoc, mul_comm, add_comm, add_left_comm] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasFDerivAt_integral_Ioi_of_contDiffAt {f : ℝ × E → F} {U : Set E} {x : E}
    {T : ℝ} {B : ℝ → ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hreg : ∀ z ∈ U, ∀ t ∈ Ioi T, ContDiffAt ℝ 1 f (t, z))
    (hint : IntegrableOn (fun t => f (t, x)) (Ioi T))
    (hB : IntegrableOn B (Ioi T))
    (hbound : ∀ z ∈ U, ∀ t ∈ Ioi T, ‖fderiv ℝ (fun y => f (t, y)) z‖ ≤ B t) :
    IntegrableOn (fun t => fderiv ℝ (fun y => f (t, y)) x) (Ioi T) ∧
      HasFDerivAt (fun y => ∫ t in Ioi T, f (t, y))
        (∫ t in Ioi T, fderiv ℝ (fun y => f (t, y)) x) x := by
  have hc (z : E) (hz : z ∈ U) : ContinuousOn (fun t => f (t, z)) (Ioi T) := by
    intro t ht
    exact ((hreg z hz t ht).continuousAt.comp (f := fun r : ℝ => (r, z))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hdc : ContinuousOn (fun t => fderiv ℝ (fun y => f (t, y)) x) (Ioi T) := by
    intro t ht
    have H := contDiffAt_partial_fderiv (hreg x hx t ht) (by norm_num : (0 : WithTop ℕ∞) + 1 ≤ 1)
    exact (H.continuousAt.comp (f := fun r : ℝ => (r, x))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  have hmeas := hdc.aestronglyMeasurable (μ := volume) measurableSet_Ioi
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi T), ‖fderiv ℝ (fun y => f (t, y)) x‖ ≤ B t :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall (fun t ht => hbound x hx t ht))
  have hnear : ∀ᶠ z in 𝓝 x, AEStronglyMeasurable (fun t => f (t, z)) (volume.restrict (Ioi T)) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact (hc z hz).aestronglyMeasurable measurableSet_Ioi
  have hbnd : ∀ᵐ t ∂volume.restrict (Ioi T), ∀ z ∈ U, ‖fderiv ℝ (fun y => f (t, y)) z‖ ≤ B t :=
    (ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall (fun t ht z hz => hbound z hz t ht))
  have hdiff : ∀ᵐ t ∂volume.restrict (Ioi T), ∀ z ∈ U,
      HasFDerivAt (fun y => f (t, y)) (fderiv ℝ (fun y => f (t, y)) z) z := by
    apply (ae_restrict_iff' measurableSet_Ioi).mpr
    exact Eventually.of_forall (fun t ht z hz =>
      (((hreg z hz t ht).comp (f := fun y : E => (t, y)) z
        (contDiffAt_const.prodMk contDiffAt_id)).differentiableAt (by norm_num)).hasFDerivAt)
  exact ⟨hB.mono' hmeas hpoint, hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun y t => f (t, y)) (F' := fun y t => fderiv ℝ (fun z => f (t, z)) y)
    (s := U) (bound := B) (hU.mem_nhds hx) hnear hint hmeas hbnd hB hdiff⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

attribute [local instance] BianchiIX.instNormedAddCommGroupContinuousLinearMapRealId_bianchiIX
attribute [local instance] BianchiIX.instNormedSpaceRealContinuousLinearMapId_bianchiIX
private theorem BianchiIX.fderiv2_integral_Ioi_of_contDiffAt {f : ℝ × E → F} {U : Set E} {x : E}
    {T : ℝ} {B : ℝ → ℝ} (hU : IsOpen U) (hx : x ∈ U)
    (hreg : ∀ z ∈ U, ∀ t ∈ Ioi T, ContDiffAt ℝ 2 f (t, z))
    (hint : ∀ z ∈ U, IntegrableOn (fun t => f (t, z)) (Ioi T))
    (hB : IntegrableOn B (Ioi T))
    (hbound1 : ∀ z ∈ U, ∀ t ∈ Ioi T, ‖fderiv ℝ (fun y => f (t, y)) z‖ ≤ B t)
    (hbound2 : ∀ z ∈ U, ∀ t ∈ Ioi T, ‖fderiv ℝ (fderiv ℝ (fun y => f (t, y))) z‖ ≤ B t) :
    IntegrableOn (fun t => fderiv ℝ (fun y => f (t, y)) x) (Ioi T) ∧
      IntegrableOn (fun t => fderiv ℝ (fderiv ℝ (fun y => f (t, y))) x) (Ioi T) ∧
      fderiv ℝ (fun y => ∫ t in Ioi T, f (t, y)) x =
        (∫ t in Ioi T, fderiv ℝ (fun y => f (t, y)) x) ∧
      fderiv ℝ (fderiv ℝ (fun y => ∫ t in Ioi T, f (t, y))) x =
        ∫ t in Ioi T, fderiv ℝ (fderiv ℝ (fun y => f (t, y))) x := by
  have hfirst (z : E) (hz : z ∈ U) := hasFDerivAt_integral_Ioi_of_contDiffAt hU hz
    (fun y hy t ht => (hreg y hy t ht).of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2))
    (hint z hz) hB hbound1
  have hsecond := hasFDerivAt_integral_Ioi_of_contDiffAt (f := fun p : ℝ × E =>
      fderiv ℝ (fun y => f (p.1, y)) p.2) hU hx
    (fun y hy t ht => contDiffAt_partial_fderiv (hreg y hy t ht) (by norm_num))
    (hfirst x hx).1 hB hbound2
  have heq : fderiv ℝ (fun y => ∫ t in Ioi T, f (t, y)) =ᶠ[𝓝 x]
      (fun y => ∫ t in Ioi T, fderiv ℝ (fun z => f (t, z)) y) := by
    filter_upwards [hU.mem_nhds hx] with z hz
    exact (hfirst z hz).2.fderiv
  exact ⟨(hfirst x hx).1, hsecond.1, (hfirst x hx).2.fderiv,
    heq.fderiv_eq.trans hsecond.2.fderiv⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_reciprocalParameter (n : WithTop ℕ∞) {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) :
    ContDiffAt ℝ n reciprocalParameter y := by unfold reciprocalParameter; fun_prop

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_reciprocalParameterMap (n : WithTop ℕ∞) {y : Fin 2 → ℝ} (hy : y 0 + 1 ≠ 0) :
    ContDiffAt ℝ n reciprocalParameterMap y := by
  unfold reciprocalParameterMap
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact contDiffAt_reciprocalParameter n hy
  · exact contDiffAt_apply ℝ ℝ 1 y

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.reciprocalParameter_range {y : Fin 2 → ℝ} (hy : 3 / 2 ≤ y 0) :
    0 < reciprocalParameter y ∧ reciprocalParameter y ≤ 2 / 5 := by
  have h : 0 < y 0 + 1 := by linarith
  refine ⟨inv_pos.mpr h, ?_⟩
  dsimp [reciprocalParameter]
  rw [← one_div]
  apply (div_le_iff₀ h).mpr
  linarith

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.product_second_derivative_bounds {f g : E → ℝ} {x : E} {A B : ℝ}
    (hf : ContDiffAt ℝ 2 f x) (hg : ContDiffAt ℝ 2 g x) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf0 : |f x| ≤ A) (hf1 : ‖fderiv ℝ f x‖ ≤ A) (hf2 : ‖fderiv ℝ (fderiv ℝ f) x‖ ≤ A)
    (hg0 : |g x| ≤ B) (hg1 : ‖fderiv ℝ g x‖ ≤ B) (hg2 : ‖fderiv ℝ (fderiv ℝ g) x‖ ≤ B) :
    |f x * g x| ≤ A * B ∧ ‖fderiv ℝ (fun y => f y * g y) x‖ ≤ 2 * A * B ∧
      ‖fderiv ℝ (fderiv ℝ (fun y => f y * g y)) x‖ ≤ 4 * A * B := by
  have hf1' (v : E) : |fderiv ℝ f x v| ≤ A * ‖v‖ :=
    ((fderiv ℝ f x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hf1 (norm_nonneg v))
  have hg1' (v : E) : |fderiv ℝ g x v| ≤ B * ‖v‖ :=
    ((fderiv ℝ g x).le_opNorm v).trans (mul_le_mul_of_nonneg_right hg1 (norm_nonneg v))
  have hf2' (v w : E) : |fderiv ℝ (fderiv ℝ f) x v w| ≤ A * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ f) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ f) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hf2 (norm_nonneg v))) (norm_nonneg w))
  have hg2' (v w : E) : |fderiv ℝ (fderiv ℝ g) x v w| ≤ B * ‖v‖ * ‖w‖ :=
    (((fderiv ℝ (fderiv ℝ g) x) v).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (((fderiv ℝ (fderiv ℝ g) x).le_opNorm v).trans
        (mul_le_mul_of_nonneg_right hg2 (norm_nonneg v))) (norm_nonneg w))
  refine ⟨by rw [abs_mul]; exact mul_le_mul hf0 hg0 (abs_nonneg _) hA, ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    rw [fderiv_fun_mul (hf.differentiableAt (by norm_num)) (hg.differentiableAt (by norm_num))]
    change |f x * fderiv ℝ g x v + g x * fderiv ℝ f x v| ≤ _
    have H := abs_add_le (f x * fderiv ℝ g x v) (g x * fderiv ℝ f x v)
    simp only [abs_mul] at H
    nlinarith only [H, mul_le_mul hf0 (hg1' v) (abs_nonneg _) hA,
      mul_le_mul hg0 (hf1' v) (abs_nonneg _) hB]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    rw [Real.norm_eq_abs, fderiv2_mul_apply hf hg]
    have htri (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c, abs_add_le (a + b + c) d]
    have H := htri (f x * fderiv ℝ (fderiv ℝ g) x v w)
      (fderiv ℝ f x v * fderiv ℝ g x w) (fderiv ℝ f x w * fderiv ℝ g x v)
      (fderiv ℝ (fderiv ℝ f) x v w * g x)
    simp only [abs_mul] at H
    nlinarith only [H, mul_le_mul hf0 (hg2' v w) (abs_nonneg _) hA,
      mul_le_mul (hf1' v) (hg1' w) (abs_nonneg _) (mul_nonneg hA (norm_nonneg v)),
      mul_le_mul (hf1' w) (hg1' v) (abs_nonneg _) (mul_nonneg hA (norm_nonneg w)),
      mul_le_mul (hf2' v w) hg0 (abs_nonneg _) (mul_nonneg (mul_nonneg hA (norm_nonneg v)) (norm_nonneg w))]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.clm_precomp_second_derivative_bounds {g : F → ℝ} {x : E} {B : ℝ}
    (L : E →L[ℝ] F) (hL : ‖L‖ ≤ 1) (hB : 0 ≤ B) (hg : ContDiffAt ℝ 2 g (L x))
    (hg1 : ‖fderiv ℝ g (L x)‖ ≤ B) (hg2 : ‖fderiv ℝ (fderiv ℝ g) (L x)‖ ≤ B) :
    ‖fderiv ℝ (g ∘ L) x‖ ≤ B ∧ ‖fderiv ℝ (fderiv ℝ (g ∘ L)) x‖ ≤ B := by
  have hLv (v : E) : ‖L v‖ ≤ ‖v‖ :=
    (L.le_opNorm v).trans (mul_le_of_le_one_left (norm_nonneg v) hL)
  have hLd : fderiv ℝ (L : E → F) = fun _ => L := funext (fun _ => L.fderiv)
  constructor
  · rw [fderiv_comp x (hg.differentiableAt (by norm_num)) L.differentiableAt]
    apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    simp only [ContinuousLinearMap.comp_apply, hLd]
    exact ((fderiv ℝ g (L x)).le_opNorm (L v)).trans (mul_le_mul hg1 (hLv v) (norm_nonneg _) hB)
  · apply ContinuousLinearMap.opNorm_le_bound _ hB
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB (norm_nonneg v))
    intro w
    have H := fderiv2_comp_apply L.contDiff.contDiffAt hg v w
    simp only [hLd, fderiv_const_apply, zero_apply, map_zero, zero_add] at H
    rw [H]
    have H0 := (((fderiv ℝ (fderiv ℝ g) (L x)) (L v)).le_opNorm (L w)).trans
      (mul_le_mul_of_nonneg_right ((fderiv ℝ (fderiv ℝ g) (L x)).le_opNorm (L v)) (norm_nonneg (L w)))
    exact H0.trans (mul_le_mul (mul_le_mul hg2 (hLv v) (norm_nonneg _) hB) (hLv w)
      (norm_nonneg _) (mul_nonneg hB (norm_nonneg v)))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_field (m u w : ℝ) :
    phaseVelocity m u 0 w = m * u ^ 2 - (m + 1) * u * w + w ^ 2 ∧
    strongVelocity m u 0 w = stableStrongRate m u w * u ∧
    activeVelocity m u 0 w = 0 ∧
    weakVelocity m u 0 w = stableWeakRate m u w * w := by
  unfold phaseVelocity strongVelocity activeVelocity weakVelocity coupling
    stableStrongRate stableWeakRate
  constructor
  · ring
  constructor
  · ring
  constructor
  · ring
  · ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stable_boundary_band {m c : ℝ} (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 10) :
    3 ≤ c + 1 ∧ 5 / 8 * (c + 1) ≤ m ∧ 0 ≤ m ∧ m ≤ c + 1 ∧
      0 ≤ m + 1 ∧ m + 1 ≤ 2 * (c + 1) := by
  obtain ⟨hl, hu⟩ := abs_le.mp hm
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  constructor <;> linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_sq (a b : ℝ) : phaseNorm a b ^ 2 = a ^ 2 + b ^ 2 :=
  Real.sq_sqrt (by positivity)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ge {a b : ℝ} (ha : 0 ≤ a) : a ≤ phaseNorm a b := by
  calc
    a = Real.sqrt (a ^ 2) := (Real.sqrt_sq ha).symm
    _ ≤ phaseNorm a b := Real.sqrt_le_sqrt (le_add_of_nonneg_right (sq_nonneg b))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_pos {a b : ℝ} (ha : 0 < a) : 0 < phaseNorm a b :=
  ha.trans_le (phaseNorm_ge ha.le)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_zero {a : ℝ} (ha : 0 ≤ a) : phaseNorm a 0 = a := by
  simp [phaseNorm, Real.sqrt_sq ha]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_defect {a b : ℝ} (ha : 0 < a) :
    phaseNorm a b - a = b ^ 2 / (phaseNorm a b + a) := by
  apply (eq_div_iff (ne_of_gt (add_pos (phaseNorm_pos ha) ha))).mpr
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.phaseNorm_ratio_defect {a b : ℝ} (ha : 0 < a) :
    1 - a / phaseNorm a b = b ^ 2 * phaseNormKernel a b := by
  have hn := ne_of_gt (phaseNorm_pos (b := b) ha)
  have hs := ne_of_gt (add_pos (phaseNorm_pos (b := b) ha) ha)
  dsimp [phaseNormKernel]
  field_simp
  nlinarith only [phaseNorm_sq a b]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_pos {m w : ℝ} (hm : -1 < m) : 0 < stableWeakRadius m w :=
  phaseNorm_pos (by linarith : 0 < m + 1)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_sq (m w : ℝ) :
    stableWeakRadius m w ^ 2 = (m + 1) ^ 2 + w ^ 2 := phaseNorm_sq _ _

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrectedPhase_zero {m : ℝ} (hm : -1 ≤ m) :
    stableCorrectedPhase m 0 0 = m := by
  simp only [stableCorrectedPhase, stableWeakRadius, phaseNorm_zero (by linarith : 0 ≤ m + 1),
    zero_pow (by norm_num : 2 ≠ 0), mul_zero, add_zero]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectionA {m : ℝ} (hm : 1 < m) :
    HasDerivAt stableCorrectionA (-(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2) m := by
  have hd : m ^ 2 - 1 ≠ 0 := by nlinarith
  convert! (hasDerivAt_id m).div (((hasDerivAt_id m).pow 2).sub_const 1) hd using 1
  dsimp
  congr 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectionC {m : ℝ} (hm : -1 < m) :
    HasDerivAt stableCorrectionC (2 / (m + 1) ^ 2) m := by
  have hd : m + 1 ≠ 0 := by linarith
  convert! (hasDerivAt_const m (-2 : ℝ)).div ((hasDerivAt_id m).add_const 1) hd using 1
  simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableWeakRadius {m w : ℝ → ℝ} {m' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hw : HasDerivAt w w' t) (hpos : -1 < m t) :
    HasDerivAt (fun s => stableWeakRadius (m s) (w s))
      (((m t + 1) * m' + w t * w') / stableWeakRadius (m t) (w t)) t := by
  have hn : (m t + 1) ^ 2 + w t ^ 2 ≠ 0 := by
    have h : 0 < m t + 1 := by linarith
    positivity
  convert! ((((hm.add_const 1).pow 2).add (hw.pow 2)).sqrt hn) using 1
  dsimp [stableWeakRadius, phaseNorm]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectedPhase {m u w : ℝ → ℝ} {m' u' w' t : ℝ}
    (hm : HasDerivAt m m' t) (hu : HasDerivAt u u' t) (hw : HasDerivAt w w' t)
    (hpos : 1 < m t) :
    HasDerivAt (fun s => stableCorrectedPhase (m s) (u s) (w s))
      (stableCorrectedGradient (m t) (u t) (w t) 0 * m' +
        stableCorrectedGradient (m t) (u t) (w t) 1 * u' +
        stableCorrectedGradient (m t) (u t) (w t) 2 * w') t := by
  have hS := hasDerivAt_stableWeakRadius hm hw (by linarith)
  have hA := (hasDerivAt_stableCorrectionA hpos).comp t hm
  have hC := (hasDerivAt_stableCorrectionC (by linarith : -1 < m t)).comp t hm
  convert! ((hS.sub_const 1).add (hA.mul (hu.pow 2))).add ((hC.mul hu).mul hw) using 1
  dsimp [stableCorrectedGradient]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_stableCorrectedPhase (n : WithTop ℕ∞) {y : Fin 3 → ℝ}
    (hm : 1 < y 0) :
    ContDiffAt ℝ n (fun z : Fin 3 → ℝ => stableCorrectedPhase (z 0) (z 1) (z 2)) y := by
  have hL : y 0 + 1 ≠ 0 := by linarith
  have hD : y 0 ^ 2 - 1 ≠ 0 := by nlinarith
  have hS : (y 0 + 1) ^ 2 + y 2 ^ 2 ≠ 0 := by
    have h : 0 < y 0 + 1 := by linarith
    positivity
  unfold stableCorrectedPhase stableWeakRadius phaseNorm stableCorrectionA stableCorrectionC
  fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_directional {m u w : ℝ} (hm : -1 < m) :
    (m + 1) / stableWeakRadius m w * phaseVelocity m u 0 w +
      w / stableWeakRadius m w * weakVelocity m u 0 w =
    (stableWeakRadius m w - (m + 1) / stableWeakRadius m w) * u ^ 2 -
      stableWeakRadius m w * u * w := by
  have hS := ne_of_gt (stableWeakRadius_pos (w := w) hm)
  rw [(stable_boundary_field m u w).1, (stable_boundary_field m u w).2.2.2]
  unfold stableWeakRate
  field_simp
  linear_combination -(u ^ 2 - u * w) * stableWeakRadius_sq m w

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_directional_quartic {m u w : ℝ} (hm : -1 < m) :
    (m + 1) / stableWeakRadius m w * phaseVelocity m u 0 w +
      w / stableWeakRadius m w * weakVelocity m u 0 w =
    m * u ^ 2 - (m + 1) * u * w +
      (stableWeakRadius m w + 1) / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1))) * u ^ 2 * w ^ 2 -
      1 / (stableWeakRadius m w + (m + 1)) * u * w ^ 3 := by
  have hL : 0 < m + 1 := by linarith
  have hS := ne_of_gt (stableWeakRadius_pos (w := w) hm)
  have hsum : stableWeakRadius m w + (m + 1) ≠ 0 :=
    ne_of_gt (add_pos (stableWeakRadius_pos hm) hL)
  have hd := phaseNorm_defect (b := w) hL
  have hr := phaseNorm_ratio_defect (b := w) hL
  change stableWeakRadius m w - (m + 1) = w ^ 2 / (stableWeakRadius m w + (m + 1)) at hd
  change 1 - (m + 1) / stableWeakRadius m w =
    w ^ 2 * (1 / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1)))) at hr
  rw [stableWeakRadius_directional hm]
  have hcoef : stableWeakRadius m w - (m + 1) / stableWeakRadius m w =
      m + (stableWeakRadius m w + 1) /
        (stableWeakRadius m w * (stableWeakRadius m w + (m + 1))) * w ^ 2 := by
    calc
      _ = m + (stableWeakRadius m w - (m + 1)) + (1 - (m + 1) / stableWeakRadius m w) := by ring
      _ = _ := by rw [hd, hr]; field_simp; ring
  rw [hcoef]
  calc
    _ = m * u ^ 2 - (m + 1) * u * w +
        (stableWeakRadius m w + 1) / (stableWeakRadius m w * (stableWeakRadius m w + (m + 1))) * u ^ 2 * w ^ 2 -
        (stableWeakRadius m w - (m + 1)) * u * w := by ring
    _ = _ := by rw [hd]; ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCorrectedPhase_directional {m u w : ℝ} (hm : 1 < m) :
    stableCorrectedGradient m u w 0 * phaseVelocity m u 0 w +
      stableCorrectedGradient m u w 1 * strongVelocity m u 0 w +
      stableCorrectedGradient m u w 2 * weakVelocity m u 0 w = stableCorrectedResidual m u w := by
  have hD : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hL : m + 1 ≠ 0 := by linarith
  have H := stableWeakRadius_directional_quartic (u := u) (w := w) (by linarith : -1 < m)
  dsimp [stableCorrectedGradient, stableCorrectedResidual, stableResidual4,
    stableResidual3, stableResidual2, stableResidual1, stableCorrectionA, stableCorrectionC]
  calc
    _ = ((m + 1) / stableWeakRadius m w * phaseVelocity m u 0 w +
          w / stableWeakRadius m w * weakVelocity m u 0 w) +
        (-(m ^ 2 + 1) / (m ^ 2 - 1) ^ 2 * u ^ 2 + 2 / (m + 1) ^ 2 * u * w) * phaseVelocity m u 0 w +
        (2 * (m / (m ^ 2 - 1)) * u + -2 / (m + 1) * w) * strongVelocity m u 0 w +
        (-2 / (m + 1) * u) * weakVelocity m u 0 w := by ring
    _ = _ := by
      rw [H]
      unfold phaseVelocity strongVelocity weakVelocity coupling
      field_simp
      ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableWeakRadius_reciprocal {m w : ℝ} (hm : -1 < m) :
    stableWeakRadius m w = (m + 1) * phaseNorm 1 ((m + 1)⁻¹ * w) := by
  have hL : 0 < m + 1 := by linarith
  have hR : 0 < phaseNorm 1 ((m + 1)⁻¹ * w) := phaseNorm_pos (by norm_num)
  have hsq := phaseNorm_sq 1 ((m + 1)⁻¹ * w)
  have hsq' : ((m + 1) * phaseNorm 1 ((m + 1)⁻¹ * w)) ^ 2 = (m + 1) ^ 2 + w ^ 2 := by
    rw [mul_pow, hsq]
    field_simp
  nlinarith only [hsq', stableWeakRadius_sq m w, stableWeakRadius_pos (w := w) hm,
    mul_pos hL hR]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualCoefficient_compactification (i : Fin 4) {m w : ℝ} (hm : 1 < m) :
    stableResidualCoefficient i ![m, w] =
      (m + 1)⁻¹ * stableResidualProfile i ![(m + 1)⁻¹, w] := by
  have hL : m + 1 ≠ 0 := by linarith
  have hD : m ^ 2 - 1 ≠ 0 := by nlinarith
  have hm1 : m - 1 ≠ 0 := by linarith
  have hden : 1 - 2 * (m + 1)⁻¹ = (m - 1) / (m + 1) := by field_simp; ring
  have hx : 1 - 2 * (m + 1)⁻¹ ≠ 0 := by
    rw [hden]
    exact div_ne_zero (by linarith) hL
  have hR : phaseNorm 1 ((m + 1)⁻¹ * w) ≠ 0 := ne_of_gt (phaseNorm_pos (by norm_num))
  have hR1 : phaseNorm 1 ((m + 1)⁻¹ * w) + 1 ≠ 0 := by
    have H := phaseNorm_pos (a := (1 : ℝ)) (b := (m + 1)⁻¹ * w) (by norm_num)
    linarith
  fin_cases i <;>
    dsimp [stableResidualCoefficient, stableResidualProfile, stableResidual4,
      stableResidual3, stableResidual2, stableResidual1] <;>
    (try rw [stableWeakRadius_reciprocal (by linarith : -1 < m)]) <;>
    (try rw [hden]) <;>
    field_simp <;> ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_stableResidualProfile (n : WithTop ℕ∞) (i : Fin 4) {p : Fin 2 → ℝ}
    (hp : p 0 < 1 / 2) : ContDiffAt ℝ n (stableResidualProfile i) p := by
  have hd : 1 - 2 * p 0 ≠ 0 := by linarith
  have hd2 := pow_ne_zero 2 hd
  have hs : (1 : ℝ) ^ 2 + (p 0 * p 1) ^ 2 ≠ 0 := ne_of_gt (by positivity)
  have hR : phaseNorm 1 (p 0 * p 1) ≠ 0 := ne_of_gt (phaseNorm_pos (by norm_num))
  have hR1 : phaseNorm 1 (p 0 * p 1) + 1 ≠ 0 := by
    have H := phaseNorm_pos (a := (1 : ℝ)) (b := p 0 * p 1) (by norm_num)
    linarith
  dsimp [phaseNorm] at hR hR1
  have hRR := mul_ne_zero hR hR1
  fin_cases i <;> unfold stableResidualProfile <;> dsimp [phaseNorm] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_stableResidualProfile_bounds :
    ∃ B > (0 : ℝ), ∀ p : Fin 2 → ℝ, (0 ≤ p 0 ∧ p 0 ≤ 2 / 5) → |p 1| ≤ 1 →
      ∀ i : Fin 4, |stableResidualProfile i p| ≤ B ∧
        ‖fderiv ℝ (stableResidualProfile i) p‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p‖ ≤ B := by
  let S : Set (Fin 2 → ℝ) := Icc ![0, -1] ![2 / 5, 1]
  have hS : IsCompact S := isCompact_Icc
  let q := fun (p : Fin 2 → ℝ) (i : Fin 4) => |stableResidualProfile i p| +
    ‖fderiv ℝ (stableResidualProfile i) p‖ + ‖fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p‖
  have hq (p : Fin 2 → ℝ) (i : Fin 4) : 0 ≤ q p i := by dsimp [q]; positivity
  have hcont (i : Fin 4) : ContinuousOn (fun p => q p i) S := by
    intro p hp
    have hreg := contDiffAt_stableResidualProfile 2 i (p := p) (by have H := hp.2 0; dsimp at H; linarith)
    have hreg' := hreg.fderiv_right (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)
    exact ((hreg.continuousAt.abs.add (hreg.continuousAt_fderiv (by norm_num)).norm).add
      (hreg'.continuousAt_fderiv (by norm_num)).norm).continuousWithinAt
  have hsum : ContinuousOn (fun p => ∑ i : Fin 4, q p i) S :=
    continuousOn_finsetSum _ (fun i _ => hcont i)
  obtain ⟨B, hB⟩ := hS.exists_bound_of_continuousOn hsum
  refine ⟨max B 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro p hp hw i
  have hpS : p ∈ S := by
    constructor
    · intro j; fin_cases j
      · exact hp.1
      · exact (abs_le.mp hw).1
    · intro j; fin_cases j
      · exact hp.2
      · exact (abs_le.mp hw).2
  have H : q p i ≤ max B 1 :=
    (Finset.single_le_sum (fun j _ => hq p j) (Finset.mem_univ i)).trans
      ((le_abs_self _).trans ((hB p hpS).trans (le_max_left _ _)))
  dsimp [q] at H
  exact ⟨by linarith [norm_nonneg (fderiv ℝ (stableResidualProfile i) p),
      norm_nonneg (fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p)],
    by linarith [abs_nonneg (stableResidualProfile i p),
      norm_nonneg (fderiv ℝ (fderiv ℝ (stableResidualProfile i)) p)],
    by linarith [abs_nonneg (stableResidualProfile i p), norm_nonneg (fderiv ℝ (stableResidualProfile i) p)]⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableResidualCoefficient_reciprocal (i : Fin 4) {y : Fin 2 → ℝ} (hy : 1 < y 0) :
    stableResidualCoefficient i y = reciprocalParameter y * stableResidualProfile i (reciprocalParameterMap y) := by
  change _ = (y 0 + 1)⁻¹ * stableResidualProfile i ![(y 0 + 1)⁻¹, y 1]
  rw [← stableResidualCoefficient_compactification i hy]
  congr 1
  ext j
  fin_cases j <;> rfl

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableResidualCoefficient_eventually_reciprocal (i : Fin 4) {y : Fin 2 → ℝ} (hy : 1 < y 0) :
    stableResidualCoefficient i =ᶠ[𝓝 y]
      (fun z => reciprocalParameter z * stableResidualProfile i (reciprocalParameterMap z)) := by
  filter_upwards [(continuous_apply 0).continuousAt.eventually (isOpen_Ioi.mem_nhds hy)] with z hz
  exact stableResidualCoefficient_reciprocal i hz

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.exists_stableResidualCoefficient_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ y : Fin 2 → ℝ, 3 / 2 ≤ y 0 → |y 1| ≤ 1 → ∀ i : Fin 4,
      ContDiffAt ℝ 2 (stableResidualCoefficient i) y ∧
        |stableResidualCoefficient i y| ≤ C / (y 0 + 1) ∧
        ‖fderiv ℝ (stableResidualCoefficient i) y‖ ≤ C / (y 0 + 1) ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualCoefficient i)) y‖ ≤ C / (y 0 + 1) := by
  obtain ⟨B, hB, HB⟩ := exists_stableResidualProfile_bounds
  refine ⟨7 * B, by positivity, ?_⟩
  intro y hy hw i
  have ha := reciprocalParameter_range hy
  have hcoords : 0 ≤ reciprocalParameterMap y 0 ∧ reciprocalParameterMap y 0 ≤ 2 / 5 := ⟨ha.1.le, ha.2⟩
  obtain ⟨h0, h1, h2⟩ := HB (reciprocalParameterMap y) hcoords hw i
  have hn : y 0 + 1 ≠ 0 := by linarith
  have hp := contDiffAt_stableResidualProfile 2 i (p := reciprocalParameterMap y) (by dsimp [reciprocalParameterMap]; linarith [ha.2])
  have heq := stableResidualCoefficient_eventually_reciprocal i (by linarith : 1 < y 0)
  have hreg := (contDiffAt_reciprocalParameter 2 hn).mul
    (hp.comp y (contDiffAt_reciprocalParameterMap 2 hn))
  refine ⟨hreg.congr_of_eventuallyEq heq, ?_⟩
  obtain ⟨H0, H1, H2⟩ := reciprocalProfile_derivative_bounds hy hB.le hp h0 h1 h2
  rw [heq.eq_of_nhds, heq.fderiv_eq, heq.fderiv.fderiv_eq]
  have hnonneg : 0 ≤ B * reciprocalParameter y := mul_nonneg hB.le ha.1.le
  simp only [reciprocalParameter, div_eq_mul_inv] at H0 H1 H2 hnonneg ⊢
  exact ⟨by nlinarith only [H0, hnonneg], by nlinarith only [H1, hnonneg], H2⟩

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.exists_stableResidualCoefficient_band_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : Fin 2 → ℝ), 2 ≤ c → |y 0 - c| ≤ 1 / 10 → |y 1| ≤ 1 →
      ∀ i : Fin 4, ContDiffAt ℝ 2 (stableResidualCoefficient i) y ∧
        |stableResidualCoefficient i y| ≤ C / (c + 1) ∧
        ‖fderiv ℝ (stableResidualCoefficient i) y‖ ≤ C / (c + 1) ∧
        ‖fderiv ℝ (fderiv ℝ (stableResidualCoefficient i)) y‖ ≤ C / (c + 1) := by
  obtain ⟨C, hC, HC⟩ := exists_stableResidualCoefficient_derivative_bounds
  refine ⟨2 * C, by positivity, ?_⟩
  intro c y hc hm hw i
  have hml := (abs_le.mp hm).1
  have hy : 3 / 2 ≤ y 0 := by linarith
  obtain ⟨hreg, h0, h1, h2⟩ := HC y hy hw i
  have H : C / (y 0 + 1) ≤ (2 * C) / (c + 1) := by
    apply (div_le_div_iff₀ (by linarith) (by linarith)).mpr
    nlinarith [hC]
  exact ⟨hreg, h0.trans H, h1.trans H, h2.trans H⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology ContDiff

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_smooth {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ ∞ (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  contDiffAt_infty.mpr (fun n => contDiffAt_normalizedMaxCurve_nat n ht)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.normalizedMaxCurve_constraint {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    stateConstraint (normalizedMaxCurve x t₀ t) = stateConstraint x := by
  simpa only [normalizedMaxCurve_initial] using
    normalized_constraint_constant (convex_normalizedMaxDomain x t₀)
      (fun _ hu => hasDerivAt_normalizedMaxCurve hu) (initial_mem_normalizedMaxDomain x t₀) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter Metric
open scoped Topology

private theorem BianchiIX.contDiffAt_normalizedMaxCurve_two {x : NormalizedState} {t₀ t : ℝ}
    (ht : t ∈ normalizedMaxDomain x t₀) :
    ContDiffAt ℝ 2 (fun z : NormalizedState × ℝ => normalizedMaxCurve z.1 t₀ z.2) (x, t) :=
  (contDiffAt_normalizedMaxCurve_smooth ht).of_le (by decide)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_projectiveOriginalFlow_time {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    HasDerivAt (projectiveOriginalFlow y t₀)
      (projectiveOriginalField (projectiveOriginalFlow y t₀ t)) t := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint (ne_of_gt hD))
  exact hasDerivAt_projectiveOriginalFlow (hasDerivAt_normalizedMaxCurve ht) (ne_of_gt hA) hc

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_projectiveOriginalFlow_two {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => projectiveOriginalFlow z.1 t₀ z.2) (y, t) := by
  have hparam : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => (fromProjectiveState z.1, z.2)) (y, t) :=
    ((contDiffAt_fromProjectiveState 2 (ne_of_gt hD)).comp (y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have hN : ContDiffAt ℝ 2 (fun z : ProjectiveState × ℝ => normalizedMaxCurve (fromProjectiveState z.1) t₀ z.2) (y, t) := by
    simpa only [Function.comp_def] using (contDiffAt_normalizedMaxCurve_two ht).comp (y, t) hparam
  simpa only [Function.comp_def, projectiveOriginalFlow] using
    (contDiffAt_toProjectiveState 2 (ne_of_gt hA)).comp (y, t) hN

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryEntry_denom_pos (m u w : ℝ) :
    0 < projectiveStateDenom (stableBoundaryEntry m u w) := by
  change 0 < projectiveDenom m u 0 w
  have H : projectiveDenom m u 0 w = 3 + m ^ 2 + (u - w) ^ 2 := by
    unfold projectiveDenom curvature
    ring
  rw [H]
  positivity

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_initial (m u w : ℝ) :
    stableBoundaryOrbit m u w 0 = stableBoundaryEntry m u w := by
  unfold stableBoundaryOrbit
  rw [normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt (stableBoundaryEntry_denom_pos m u w))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_global {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    ∀ t ≥ 0,
      3 / (c + 1) ^ 2 ≤ normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 t ∧
      stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
      |stableBoundaryOrbit m u w t 0 - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) ∧
      |stableBoundaryOrbit m u w t 1| ≤ |u| ∧ |stableBoundaryOrbit m u w t 3| ≤ |w| := by
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate (fromProjectiveState (stableBoundaryEntry m u w)) 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_global_region hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  have H' := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  change ∀ t ≥ 0, _ ∧ stableBoundaryRegion c (stableBoundaryOrbit m u w t) ∧
    |stableBoundaryOrbit m u w t 0 - stableBoundaryOrbit m u w 0 0| ≤
      8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) ∧
    |stableBoundaryOrbit m u w t 1| ≤ |stableBoundaryOrbit m u w 0 1| ∧
    |stableBoundaryOrbit m u w t 3| ≤ |stableBoundaryOrbit m u w 0 3| at H'
  simpa [hi, stableBoundaryEntry] using H'

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_exists {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    Tendsto (fun t => stableBoundaryOrbit m u w t 0) atTop (𝓝 (stableBoundaryProjection m u w)) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 1) atTop (𝓝 0) ∧
    Tendsto (fun t => stableBoundaryOrbit m u w t 3) atTop (𝓝 0) ∧
    (∀ t ≥ 0, |stableBoundaryProjection m u w - stableBoundaryOrbit m u w t 0| ≤
      8 * (|stableBoundaryOrbit m u w t 1| + |stableBoundaryOrbit m u w t 3|) ^ 2 / (c + 1)) ∧
    |stableBoundaryProjection m u w - m| ≤ 8 * (|u| + |w|) ^ 2 / (c + 1) := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hD := stableBoundaryEntry_denom_pos m u w
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt hD)
  have hA : 0 < normalizedProjectiveRate x 0 0 := by
    unfold normalizedProjectiveRate
    rw [normalizedMaxCurve_initial]
    exact fromProjectiveState_clock_pos hD
  have hi := stableBoundaryOrbit_initial m u w
  have H := normalized_stable_limit hx hc (le_refl 0) hA
  change |stableBoundaryOrbit m u w 0 0 - c| ≤ 1 / 40 →
    |stableBoundaryOrbit m u w 0 1| ≤ 1 / 200 → stableBoundaryOrbit m u w 0 2 = 0 →
    |stableBoundaryOrbit m u w 0 3| ≤ 1 / 200 → _ at H
  obtain ⟨P, hP, hU, hW, htail⟩ := H (by simpa [hi, stableBoundaryEntry] using hm)
    (by simpa [hi, stableBoundaryEntry] using hu) (by simp [hi, stableBoundaryEntry])
    (by simpa [hi, stableBoundaryEntry] using hw)
  have heq : stableBoundaryProjection m u w = P := hP.limUnder_eq
  rw [heq]
  refine ⟨hP, hU, hW, htail, ?_⟩
  have H0 := htail 0 le_rfl
  change |P - stableBoundaryOrbit m u w 0 0| ≤
    8 * (|stableBoundaryOrbit m u w 0 1| + |stableBoundaryOrbit m u w 0 3|) ^ 2 / (c + 1) at H0
  simpa [hi, stableBoundaryEntry] using H0

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableBoundaryOrbit_two {y : Fin 3 → ℝ} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (fun z : (Fin 3 → ℝ) × ℝ => stableBoundaryOrbit (z.1 0) (z.1 1) (z.1 2) z.2) (y, t) := by
  have hD := stableBoundaryEntry_denom_pos (y 0) (y 1) (y 2)
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hK : 0 < c + 1 := by linarith
  have hA := lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2)
    (stableBoundaryOrbit_global hc hm hu hw t ht).1
  have hentry : ContDiffAt ℝ 2
      (fun z : (Fin 3 → ℝ) × ℝ => (stableBoundaryEntry (z.1 0) (z.1 1) (z.1 2), z.2)) (y, t) := by
    apply ContDiffAt.prodMk _ contDiffAt_snd
    apply contDiffAt_pi.mpr
    intro i
    fin_cases i <;> dsimp [stableBoundaryEntry] <;> fun_prop
  have H := (contDiffAt_projectiveOriginalFlow_two hD hdom hA).comp (y, t) hentry
  exact H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryProjection_band {m c u w : ℝ}
    (hc : 2 ≤ c) (hm : |m - c| ≤ 1 / 40)
    (hu : |u| ≤ 1 / 200) (hw : |w| ≤ 1 / 200) :
    |stableBoundaryProjection m u w - c| ≤ 1 / 10 := by
  apply le_of_tendsto (((stableBoundaryProjection_exists hc hm hu hw).1.sub_const c).abs)
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
  exact (stableBoundaryOrbit_global hc hm hu hw t ht).2.1.1

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_apply (y : StableState) : stableInclusion y = ![y 0, y 1, 0, y 2] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRestriction_apply (y : ProjectiveState) : stableRestriction y = ![y 0, y 1, y 3] := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_entry (y : StableState) :
    stableInclusion y = stableBoundaryEntry (y 0) (y 1) (y 2) := stableInclusion_apply y

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableRestriction_inclusion (y : StableState) : stableRestriction (stableInclusion y) = y := by
  ext i
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableInclusion_restriction {y : ProjectiveState} (hy : y 2 = 0) :
    stableInclusion (stableRestriction y) = y := by
  ext i
  fin_cases i
  · rfl
  · rfl
  · exact hy.symm
  · rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_pos (y : StableState) : 0 < stableBoundaryDenom y := by
  unfold stableBoundaryDenom
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_eq (y : StableState) :
    projectiveStateDenom (stableInclusion y) = stableBoundaryDenom y := by
  change projectiveDenom (y 0) (y 1) 0 (y 2) = _
  unfold projectiveDenom curvature stableBoundaryDenom
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryField_inclusion (y : StableState) :
    projectiveField (stableInclusion y) = stableInclusion (stableBoundaryField y) := by
  obtain ⟨hM, hU, hV, hW⟩ := stable_boundary_field (y 0) (y 1) (y 2)
  ext i
  fin_cases i
  · exact hM
  · exact hU
  · exact hV
  · exact hW

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_inclusion (y : StableState) :
    projectiveOriginalField (stableInclusion y) = stableInclusion (stableOriginalField y) := by
  rw [projectiveOriginalField, stableBoundaryDenom_eq, stableBoundaryField_inclusion,
    stableOriginalField, map_smul]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableOriginalField_restriction {y : ProjectiveState} (hy : y 2 = 0) :
    stableRestriction (projectiveOriginalField y) = stableOriginalField (stableRestriction y) := by
  rw [← stableInclusion_restriction hy, stableOriginalField_inclusion, stableRestriction_inclusion,
    stableRestriction_inclusion]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableBoundaryDenom (n : WithTop ℕ∞) : ContDiff ℝ n stableBoundaryDenom := by
  unfold stableBoundaryDenom
  fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableCorrectedPhase_scaled {Y : ℝ → ProjectiveState} {a t : ℝ}
    (hY : HasDerivAt Y (a • projectiveField (Y t)) t) (hm : 1 < Y t 0) (hv : Y t 2 = 0) :
    HasDerivAt (fun s => stableCorrectedPhase (Y s 0) (Y s 1) (Y s 3))
      (a * stableCorrectedResidual (Y t 0) (Y t 1) (Y t 3)) t := by
  have H := hasDerivAt_stableCorrectedPhase (hasDerivAt_pi.mp hY 0)
    (hasDerivAt_pi.mp hY 1) (hasDerivAt_pi.mp hY 3) hm
  convert! H using 1
  simp only [Pi.smul_apply, smul_eq_mul]
  change _ = _ * (a * phaseVelocity _ _ _ _) + _ * (a * strongVelocity _ _ _ _) + _ * (a * weakVelocity _ _ _ _)
  rw [hv, ← stableCorrectedPhase_directional hm]
  ring

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableBoundaryOrbit_active_zero (m u w : ℝ) {t : ℝ} (ht : 0 ≤ t) :
    stableBoundaryOrbit m u w t 2 = 0 := by
  let x := fromProjectiveState (stableBoundaryEntry m u w)
  have hx : stateConstraint x = 1 := fromProjectiveState_constraint (ne_of_gt (stableBoundaryEntry_denom_pos m u w))
  have hzero : wallValue 1 x = 0 := by
    simp [x, wallValue, fromProjectiveState, stableBoundaryEntry]
  have H := (normalizedMaxCurve_wall_sign hx ht 1).1.mpr hzero
  change normalizedMaxCurve x 0 t 3 = 0 at H
  change Real.sqrt 3 * normalizedMaxCurve x 0 t 3 / (1 + normalizedMaxCurve x 0 t 0) = 0
  rw [H, mul_zero, zero_div]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_eq (y : StableState) (t : ℝ) :
    stableOriginalFlow y t = stableRestriction (stableBoundaryOrbit (y 0) (y 1) (y 2) t) := by
  simp only [stableOriginalFlow, stableInclusion_entry, projectiveOriginalFlow, stableBoundaryOrbit]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableProjectiveFlow_active_zero (y : StableState) {t : ℝ} (ht : 0 ≤ t) :
    projectiveOriginalFlow (stableInclusion y) 0 t 2 = 0 := by
  simpa only [stableInclusion_entry, projectiveOriginalFlow, stableBoundaryOrbit] using
    stableBoundaryOrbit_active_zero (y 0) (y 1) (y 2) ht

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableProjectiveFlow_rate_pos {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    0 < normalizedProjectiveRate (fromProjectiveState (stableInclusion y)) 0 t := by
  have hK : 0 < c + 1 := by linarith
  rw [stableInclusion_entry]
  exact lt_of_lt_of_le (by positivity : 0 < 3 / (c + 1) ^ 2)
    (stableBoundaryOrbit_global hc hm hu hw t ht).1

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_initial (y : StableState) : stableOriginalFlow y 0 = y := by
  rw [stableOriginalFlow_eq, stableBoundaryOrbit_initial, ← stableInclusion_entry]
  exact stableRestriction_inclusion y

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableOriginalFlow {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    HasDerivAt (stableOriginalFlow y) (stableOriginalField (stableOriginalFlow y t)) t := by
  have hD : 0 < projectiveStateDenom (stableInclusion y) := by
    rw [stableBoundaryDenom_eq]
    exact stableBoundaryDenom_pos y
  have hx := fromProjectiveState_constraint (ne_of_gt hD)
  have hdom := normalizedMaxDomain_contains_Ici_of_constraint hx 0 ht
  have hA := stableProjectiveFlow_rate_pos hc hm hu hw ht
  have H := stableRestriction.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_projectiveOriginalFlow_time hD hdom hA)
  rw [stableOriginalField_restriction (stableProjectiveFlow_active_zero y ht)] at H
  exact H

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableBoundaryDenom {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) :
    HasDerivAt (fun s => stableBoundaryDenom (gamma s))
      (dotProduct (stableDenomGradient (gamma t)) v) t := by
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  apply (((hm.pow 2).const_add 3).add ((hu.sub hw).pow 2)).congr_deriv
  simp [stableDenomGradient, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_dotProduct (y v : StableState) :
    dotProduct (stableDenomGradient y) v =
      2 * y 0 * v 0 + 2 * (y 1 - y 2) * (v 1 - v 2) := by
  simp [stableDenomGradient, dotProduct, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableDenomGradient_dotProduct
    {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (w : StableState) :
    HasDerivAt (fun s => dotProduct (stableDenomGradient (gamma s)) w)
      (stableDenomHessian v w) t := by
  simp only [stableDenomGradient_dotProduct]
  have hm := hasDerivAt_pi.mp h 0
  have hu := hasDerivAt_pi.mp h 1
  have hw := hasDerivAt_pi.mp h 2
  exact ((hm.const_mul 2).mul_const (w 0)).add
    (((hu.sub hw).const_mul 2).mul_const (w 1 - w 2))

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledFlow_initial (K : ℝ) (y : StableState) : stableRescaledFlow K y 0 = y := by
  simp only [stableRescaledFlow, mul_zero, stableOriginalFlow_initial]

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_stableRescaledFlow {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasDerivAt (stableRescaledFlow K y) (K • stableOriginalField (stableRescaledFlow K y s)) s := by
  exact (hasDerivAt_stableOriginalFlow hc hm hu hw (mul_nonneg hK.le hs)).scomp s
    (by simpa using (hasDerivAt_id s).const_mul K)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableOriginalFlow_two {y : StableState} {c t : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (ht : 0 ≤ t) :
    ContDiffAt ℝ 2 (fun z : StableState × ℝ => stableOriginalFlow z.1 z.2) (y, t) := by
  simp_rw [stableOriginalFlow_eq]
  exact stableRestriction.contDiff.contDiffAt.comp (y, t)
    (contDiffAt_stableBoundaryOrbit_two hc hm hu hw ht)

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_stableRescaledFlow_two {K : ℝ} {y : StableState} {c s : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (fun z : StableState × ℝ => stableRescaledFlow K z.1 z.2) (y, s) := by
  have H := contDiffAt_stableOriginalFlow_two hc hm hu hw (mul_nonneg hK.le hs)
  have hmap : ContDiffAt ℝ 2 (fun z : StableState × ℝ => (z.1, K * z.2)) (y, s) :=
    contDiffAt_fst.prodMk (contDiffAt_const.mul contDiffAt_snd)
  have H' := H.comp (y, s) hmap
  exact H'

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableOriginalFlow_limit {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Tendsto (stableOriginalFlow y) atTop (𝓝 ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) := by
  have H := stableBoundaryProjection_exists hc hm hu hw
  apply tendsto_pi_nhds.mpr
  intro i
  simp_rw [stableOriginalFlow_eq, stableRestriction_apply]
  fin_cases i
  · exact H.1
  · exact H.2.1
  · exact H.2.2.1

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology

private theorem BianchiIX.stableRescaledFlow_limit {K : ℝ} {y : StableState} {c : ℝ}
    (hK : 0 < K) (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    Tendsto (stableRescaledFlow K y) atTop (𝓝 ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) :=
  (stableOriginalFlow_limit hc hm hu hw).comp (Tendsto.const_mul_atTop hK tendsto_id)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.stableRescaledFlow_band {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    |stableRescaledFlow (c + 1) y s 0 - c| ≤ 1 / 10 ∧
    |stableRescaledFlow (c + 1) y s 1| ≤ 1 / 100 ∧
    |stableRescaledFlow (c + 1) y s 2| ≤ 1 / 100 := by
  have ht : 0 ≤ (c + 1) * s := mul_nonneg (by linarith) hs
  have H := (stableBoundaryOrbit_global hc hm hu hw ((c + 1) * s) ht).2.1
  simp only [stableRescaledFlow, stableOriginalFlow_eq, stableRestriction_apply]
  exact ⟨H.1, H.2.1, H.2.2.2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableBoundaryDenom_lower {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    (c + 1) ^ 2 ≤ 3 * stableBoundaryDenom y ∧ c + 1 ≤ stableBoundaryDenom y := by
  obtain ⟨hK, hml, hm0, _, _, _⟩ := stable_boundary_band hc hm
  have hm2 := (sq_le_sq₀ (by positivity : 0 ≤ (5 / 8 : ℝ) * (c + 1)) hm0).mpr hml
  unfold stableBoundaryDenom
  constructor
  · nlinarith [sq_nonneg (y 1 - y 2)]
  · nlinarith [sq_nonneg (y 1 - y 2), sq_nonneg (c + 1 - 3)]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_wall_bound (y : StableState) (j : Fin 3) (hj : j ≠ 0) :
    |stableDenomGradient y j| ≤ 2 * (|y 1| + |y 2|) := by
  fin_cases j
  · exact (hj rfl).elim
  · change |2 * (y 1 - y 2)| ≤ _
    rw [abs_mul]
    norm_num only
    exact mul_le_mul_of_nonneg_left (abs_sub _ _) (by norm_num)
  · change |2 * (y 2 - y 1)| ≤ _
    rw [abs_mul]
    norm_num only
    have H := abs_sub (y 2) (y 1)
    linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |dotProduct (stableDenomGradient y) v| ≤ 6 * (c + 1) * ‖v‖ := by
  obtain ⟨hK, _, hm0, hmK, _, _⟩ := stable_boundary_band hc hm
  have hg (j : Fin 3) : |stableDenomGradient y j| ≤ 2 * (c + 1) := by
    by_cases hj : j = 0
    · subst j
      change |2 * y 0| ≤ _
      rw [abs_of_nonneg (by positivity)]
      linarith
    · exact (stableDenomGradient_wall_bound y j hj).trans (by linarith)
  have hv (j : Fin 3) : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  have hprod (j : Fin 3) : |stableDenomGradient y j * v j| ≤ 2 * (c + 1) * ‖v‖ := by
    rw [abs_mul]
    exact mul_le_mul (hg j) (hv j) (abs_nonneg _) (by positivity)
  calc
    _ ≤ ∑ j, |stableDenomGradient y j * v j| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin 3, 2 * (c + 1) * ‖v‖ := Finset.sum_le_sum (fun j _ => hprod j)
    _ = _ := by simp; ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomHessian_bound (v w : StableState) :
    |stableDenomHessian v w| ≤ 10 * ‖v‖ * ‖w‖ := by
  have hv (j : Fin 3) : |v j| ≤ ‖v‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm v j
  have hw (j : Fin 3) : |w j| ≤ ‖w‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm w j
  have hvd : |v 1 - v 2| ≤ 2 * ‖v‖ := (abs_sub _ _).trans (by linarith [hv 1, hv 2])
  have hwd : |w 1 - w 2| ≤ 2 * ‖w‖ := (abs_sub _ _).trans (by linarith [hw 1, hw 2])
  have H0 := mul_le_mul (hv 0) (hw 0) (abs_nonneg _) (norm_nonneg _)
  have H1 := mul_le_mul hvd hwd (abs_nonneg _) (by positivity)
  have H := abs_add_le (2 * v 0 * w 0) (2 * (v 1 - v 2) * (w 1 - w 2))
  simp only [abs_mul] at H
  norm_num only at H
  change |stableDenomHessian v w| ≤ _ at H
  nlinarith only [H, H0, H1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableTangent_split_bounds (v : StableState) :
    ‖(![v 0, 0, 0] : StableState)‖ ≤ ‖v‖ ∧
      ‖(![0, v 1, v 2] : StableState)‖ ≤ ‖![v 1, v 2]‖ ∧ ‖![v 1, v 2]‖ ≤ ‖v‖ := by
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 0
    · simp
    · simp
  constructor
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro i
    fin_cases i
    · simp
    · exact norm_le_pi_norm ![v 1, v 2] 0
    · exact norm_le_pi_norm ![v 1, v 2] 1
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg v)).mpr
    intro i
    fin_cases i
    · exact norm_le_pi_norm v 1
    · exact norm_le_pi_norm v 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiff_stableResidualClock (n : WithTop ℕ∞) (K : ℝ) :
    ContDiff ℝ n (stableResidualClock K) := by
  unfold stableResidualClock
  exact contDiff_const.div (contDiff_stableBoundaryDenom n) (fun y => (stableBoundaryDenom_pos y).ne')

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableResidualClock {gamma : ℝ → StableState} {v : StableState} {t : ℝ}
    (h : HasDerivAt gamma v t) (K : ℝ) :
    HasDerivAt (fun s => stableResidualClock K (gamma s))
      (-(6 * K / stableBoundaryDenom (gamma t) ^ 2) * dotProduct (stableDenomGradient (gamma t)) v) t := by
  have H := (hasDerivAt_const t (6 * K)).div (hasDerivAt_stableBoundaryDenom h)
    (stableBoundaryDenom_pos (gamma t)).ne'
  convert! H using 1
  simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_fderiv (K : ℝ) (y v : StableState) :
    fderiv ℝ (stableResidualClock K) y v =
      -(6 * K / stableBoundaryDenom y ^ 2) * dotProduct (stableDenomGradient y) v := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableResidualClock 1 K).differentiable (by norm_num) y).hasFDerivAt
  have H := (show HasFDerivAt (stableResidualClock K) (fderiv ℝ (stableResidualClock K) y)
      (y + (0 : ℝ) • v) by simpa using hd).comp_hasDerivAt 0 hl
  simpa only [zero_smul, add_zero] using H.unique (hasDerivAt_stableResidualClock hl K)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_fderiv2 (K : ℝ) (y v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableResidualClock K)) y v w =
      stableResidualClock K y *
        (2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
          (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y) -
          stableDenomHessian v w / stableBoundaryDenom y) := by
  have hl : HasDerivAt (fun s : ℝ => y + s • v) v 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add ((hasDerivAt_id (0 : ℝ)).smul_const v) using 1
    simp
  have hd := ((contDiff_stableResidualClock 2 K).fderiv_right
    (by norm_num : (1 : WithTop ℕ∞) + 1 ≤ 2)).differentiable (by norm_num)
  have Hleft := hasDerivAt_fderiv_apply_const (hd (y + (0 : ℝ) • v)) hl w
  simp only [stableResidualClock_fderiv] at Hleft
  have hD := hasDerivAt_stableBoundaryDenom hl
  have hG := hasDerivAt_stableDenomGradient_dotProduct hl w
  have Hright := (((hasDerivAt_const (0 : ℝ) (6 * K)).div (hD.pow 2)
    (pow_ne_zero 2 (stableBoundaryDenom_pos _).ne')).neg).mul hG
  have H := Hleft.unique Hright
  simp only [Pi.pow_apply, Pi.div_apply, Pi.neg_apply, zero_smul, add_zero] at H
  rw [H]
  unfold stableResidualClock
  have hn := (stableBoundaryDenom_pos y).ne'
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10) :
    |stableResidualClock (c + 1) y| ≤ 18 / (c + 1) := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  rw [stableResidualClock, abs_of_pos (by positivity)]
  apply (div_le_div_iff₀ hD hK).mpr
  nlinarith [(stableBoundaryDenom_lower hc hm).1]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableDenomGradient_ratio_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |dotProduct (stableDenomGradient y) v / stableBoundaryDenom y| ≤ 6 * ‖v‖ := by
  rw [abs_div, abs_of_pos (stableBoundaryDenom_pos y)]
  apply (div_le_iff₀ (stableBoundaryDenom_pos y)).mpr
  have H := mul_le_mul_of_nonneg_right (stableBoundaryDenom_lower hc hm).2 (show 0 ≤ 6 * ‖v‖ by positivity)
  nlinarith only [H, stableDenomGradient_bound hc hm hu hw v]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_first_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v : StableState) :
    |fderiv ℝ (stableResidualClock (c + 1)) y v| ≤ 108 / (c + 1) * ‖v‖ := by
  have hK : 0 < c + 1 := by linarith
  rw [stableResidualClock_fderiv]
  have heq : -(6 * (c + 1) / stableBoundaryDenom y ^ 2) * dotProduct (stableDenomGradient y) v =
      -stableResidualClock (c + 1) y * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) := by
    unfold stableResidualClock
    ring
  rw [heq, abs_mul, abs_neg]
  have H := mul_le_mul (stableResidualClock_bound hc hm) (stableDenomGradient_ratio_bound hc hm hu hw v)
    (abs_nonneg _) (by positivity : 0 ≤ 18 / (c + 1))
  convert! H using 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_second_bound {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) (v w : StableState) :
    |fderiv ℝ (fderiv ℝ (stableResidualClock (c + 1))) y v w| ≤ 1476 / (c + 1) * ‖v‖ * ‖w‖ := by
  have hK : 0 < c + 1 := by linarith
  have hD := stableBoundaryDenom_pos y
  have hD1 : 1 ≤ stableBoundaryDenom y := by
    have H := (stableBoundaryDenom_lower hc hm).2
    linarith
  have H1 := mul_le_mul (stableDenomGradient_ratio_bound hc hm hu hw v)
    (stableDenomGradient_ratio_bound hc hm hu hw w) (abs_nonneg _) (by positivity : 0 ≤ 6 * ‖v‖)
  have H2 : |stableDenomHessian v w / stableBoundaryDenom y| ≤ 10 * ‖v‖ * ‖w‖ := by
    rw [abs_div, abs_of_pos hD]
    apply (div_le_iff₀ hD).mpr
    have H := mul_le_mul_of_nonneg_left hD1 (show 0 ≤ 10 * ‖v‖ * ‖w‖ by positivity)
    nlinarith only [H, stableDenomHessian_bound v w]
  have H3 : |2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
      (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y) -
      stableDenomHessian v w / stableBoundaryDenom y| ≤ 82 * ‖v‖ * ‖w‖ := by
    have H := abs_sub (2 * (dotProduct (stableDenomGradient y) v / stableBoundaryDenom y) *
      (dotProduct (stableDenomGradient y) w / stableBoundaryDenom y)) (stableDenomHessian v w / stableBoundaryDenom y)
    simp only [abs_mul] at H
    norm_num only at H
    nlinarith only [H, H1, H2]
  rw [stableResidualClock_fderiv2, abs_mul]
  have H := mul_le_mul (stableResidualClock_bound hc hm) H3 (abs_nonneg _) (by positivity : 0 ≤ 18 / (c + 1))
  convert! H using 1
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableResidualClock_derivative_bounds {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 10)
    (hu : |y 1| ≤ 1 / 100) (hw : |y 2| ≤ 1 / 100) :
    |stableResidualClock (c + 1) y| ≤ 1500 / (c + 1) ∧
      ‖fderiv ℝ (stableResidualClock (c + 1)) y‖ ≤ 1500 / (c + 1) ∧
      ‖fderiv ℝ (fderiv ℝ (stableResidualClock (c + 1))) y‖ ≤ 1500 / (c + 1) := by
  have hK : 0 < c + 1 := by linarith
  refine ⟨(stableResidualClock_bound hc hm).trans (div_le_div_of_nonneg_right (by norm_num) hK.le), ?_, ?_⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    exact (stableResidualClock_first_bound hc hm hu hw v).trans
      (mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (by norm_num) hK.le) (norm_nonneg v))
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    exact (stableResidualClock_second_bound hc hm hu hw v w).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right (by norm_num) hK.le) (norm_nonneg v)) (norm_nonneg w))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCenterWeakProjection_apply (y : StableState) :
    stableCenterWeakProjection y = ![y 0, y 2] := by ext i; fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableCenterWeakProjection_norm : ‖stableCenterWeakProjection‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro y
  rw [one_mul, stableCenterWeakProjection_apply]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg y)).mpr
  intro i; fin_cases i
  · exact norm_le_pi_norm y 0
  · exact norm_le_pi_norm y 2

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_stableScaledResidualCoefficient_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 → ∀ i : Fin 4,
      ContDiffAt ℝ 2 (stableScaledResidualCoefficient (c + 1) i) y ∧
        |stableScaledResidualCoefficient (c + 1) i y| ≤ C / (c + 1) ^ 2 ∧
        ‖fderiv ℝ (stableScaledResidualCoefficient (c + 1) i) y‖ ≤ C / (c + 1) ^ 2 ∧
        ‖fderiv ℝ (fderiv ℝ (stableScaledResidualCoefficient (c + 1) i)) y‖ ≤ C / (c + 1) ^ 2 := by
  obtain ⟨C, hC, HC⟩ := exists_stableResidualCoefficient_band_derivative_bounds
  refine ⟨6000 * C, by positivity, ?_⟩
  intro c y hc hm hu hw i
  have hK : 0 < c + 1 := by linarith
  have hmw : |stableCenterWeakProjection y 0 - c| ≤ 1 / 10 := hm
  have hww : |stableCenterWeakProjection y 1| ≤ 1 := by change |y 2| ≤ 1; linarith
  obtain ⟨hg, hg0, hg1, hg2⟩ := HC c (stableCenterWeakProjection y) hc hmw hww i
  have hpre := clm_precomp_second_derivative_bounds stableCenterWeakProjection stableCenterWeakProjection_norm
    (by positivity : 0 ≤ C / (c + 1)) hg hg1 hg2
  have hcomp : ContDiffAt ℝ 2 (stableResidualCoefficient i ∘ stableCenterWeakProjection) y :=
    hg.comp y stableCenterWeakProjection.contDiff.contDiffAt
  obtain ⟨hq0, hq1, hq2⟩ := stableResidualClock_derivative_bounds hc hm hu hw
  have hreg : ContDiffAt ℝ 2 (stableResidualClock (c + 1)) y :=
    (contDiff_stableResidualClock 2 (c + 1)).contDiffAt
  obtain ⟨H0, H1, H2⟩ := product_second_derivative_bounds hreg hcomp
    (by positivity : 0 ≤ 1500 / (c + 1)) (by positivity : 0 ≤ C / (c + 1))
    hq0 hq1 hq2 hg0 hpre.1 hpre.2
  have hsame : stableScaledResidualCoefficient (c + 1) i =
      (fun z => stableResidualClock (c + 1) z * (stableResidualCoefficient i ∘ stableCenterWeakProjection) z) := rfl
  rw [hsame]
  refine ⟨hreg.mul hcomp, ?_⟩
  have hnonneg : 0 ≤ C / (c + 1) ^ 2 := by positivity
  simp only [div_eq_mul_inv, ← inv_pow] at H0 H1 H2 hnonneg ⊢
  exact ⟨by nlinarith only [H0, hnonneg], by nlinarith only [H1, hnonneg], by nlinarith only [H2]⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_factor (K : ℝ) (y : StableState) :
    stableScaledResidual K y = y 1 * stableScaledResidualCubic K y := by
  simp [stableScaledResidual, stableScaledResidualCubic, stableScaledResidualCoefficient,
    stableResidualCoefficient, stableCenterWeakProjection_apply, stableCubicMonomial,
    stableCorrectedResidual, Fin.sum_univ_succ]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_stableScaledResidualCubic_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 →
      ContDiffAt ℝ 2 (stableScaledResidualCubic (c + 1)) y ∧
        |stableScaledResidualCubic (c + 1) y| ≤ C / (c + 1) ^ 2 * (|y 1| + |y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableScaledResidualCubic (c + 1)) y v| ≤ C / (c + 1) ^ 2 * stableCubicFirstBudget y v) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidualCubic (c + 1))) y v w| ≤ C / (c + 1) ^ 2 * stableCubicSecondBudget y v w) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidualCoefficient_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro c y hc hm hu hw
  have H := stableScaledResidualCubic_bounds_of_coefficients (by positivity : 0 ≤ C / (c + 1) ^ 2) (HC c y hc hm hu hw)
  have hscale : 4 * (C / (c + 1) ^ 2) = 4 * C / (c + 1) ^ 2 := by ring
  simpa only [hscale] using H

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.isOpen_stableParameterDomain (c : ℝ) : IsOpen (stableParameterDomain c) :=
  (isOpen_lt ((continuous_apply 0).sub continuous_const).abs continuous_const).inter
    ((isOpen_lt (continuous_apply 1).abs continuous_const).inter
      (isOpen_lt (continuous_apply 2).abs continuous_const))

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableFirstInputWeight_nonneg {b : ℝ} (hb : 0 ≤ b) (v : StableState) :
    0 ≤ stableFirstInputWeight b v := by unfold stableFirstInputWeight; positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableFirstInputWeight_center (b : ℝ) {v : StableState} (hv1 : v 1 = 0) (hv2 : v 2 = 0) :
    stableFirstInputWeight b v = b * ‖v‖ := by simp [stableFirstInputWeight, hv1, hv2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableFirstInputWeight_le {b : ℝ} (hb : b ≤ 1) (v : StableState) :
    stableFirstInputWeight b v ≤ 2 * ‖v‖ := by
  have H := mul_le_mul_of_nonneg_right hb (norm_nonneg v)
  have Hz := (stableTangent_split_bounds v).2.2
  unfold stableFirstInputWeight
  linarith

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_contDiffAt {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) :
    ContDiffAt ℝ 2 (stableScaledResidual K) y := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq]
  exact (contDiffAt_apply ℝ ℝ 1 y).mul hg

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_fderiv {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) (v : StableState) :
    fderiv ℝ (stableScaledResidual K) y v =
      v 1 * stableScaledResidualCubic K y + y 1 * fderiv ℝ (stableScaledResidualCubic K) y v := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq, fderiv_fun_mul ((contDiffAt_apply (n := 1) ℝ ℝ 1 y).differentiableAt (by norm_num))
    (hg.differentiableAt (by norm_num))]
  have hp : fderiv ℝ (fun z : StableState => z 1) y =
      (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ) :=
    (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ).fderiv
  rw [hp]
  change y 1 * fderiv ℝ (stableScaledResidualCubic K) y v + stableScaledResidualCubic K y * v 1 = _
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_fderiv2 {K : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableScaledResidual K)) y v w =
      v 1 * fderiv ℝ (stableScaledResidualCubic K) y w +
        w 1 * fderiv ℝ (stableScaledResidualCubic K) y v +
        y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w := by
  have heq : stableScaledResidual K = fun z => z 1 * stableScaledResidualCubic K z :=
    funext (stableScaledResidual_factor K)
  rw [heq, fderiv2_mul_apply (contDiffAt_apply ℝ ℝ 1 y) hg]
  have hp : fderiv ℝ (fun z : StableState => z 1) =
      fun _ => (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ) :=
    funext (fun _ => (ContinuousLinearMap.proj 1 : StableState →L[ℝ] ℝ).fderiv)
  simp only [hp, fderiv_const_apply, zero_apply, zero_mul, add_zero]
  change y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w +
    v 1 * fderiv ℝ (stableScaledResidualCubic K) y w +
    w 1 * fderiv ℝ (stableScaledResidualCubic K) y v = _
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.stableScaledResidual_bounds_of_cubic {K B : ℝ} {y : StableState}
    (hg : ContDiffAt ℝ 2 (stableScaledResidualCubic K) y)
    (h0 : |stableScaledResidualCubic K y| ≤ B * (|y 1| + |y 2|) ^ 3)
    (h1 : ∀ v, |fderiv ℝ (stableScaledResidualCubic K) y v| ≤ B * stableCubicFirstBudget y v)
    (h2 : ∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w| ≤ B * stableCubicSecondBudget y v w) :
    |stableScaledResidual K y| ≤ B * |y 1| * (|y 1| + |y 2|) ^ 3 ∧
      (∀ v, |fderiv ℝ (stableScaledResidual K) y v| ≤
        B * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v)) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidual K)) y v w| ≤
        B * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
          |y 1| * stableCubicSecondBudget y v w)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [stableScaledResidual_factor, abs_mul]
    have H := mul_le_mul_of_nonneg_left h0 (abs_nonneg (y 1))
    nlinarith only [H]
  · intro v
    rw [stableScaledResidual_fderiv hg]
    have H := abs_add_le (v 1 * stableScaledResidualCubic K y)
      (y 1 * fderiv ℝ (stableScaledResidualCubic K) y v)
    simp only [abs_mul] at H
    have H0 := mul_le_mul_of_nonneg_left h0 (abs_nonneg (v 1))
    have H1 := mul_le_mul_of_nonneg_left (h1 v) (abs_nonneg (y 1))
    nlinarith only [H, H0, H1]
  · intro v w
    rw [stableScaledResidual_fderiv2 hg]
    have htri (a b c : ℝ) : |a + b + c| ≤ |a| + |b| + |c| := by
      linarith only [abs_add_le a b, abs_add_le (a + b) c]
    have H := htri (v 1 * fderiv ℝ (stableScaledResidualCubic K) y w)
      (w 1 * fderiv ℝ (stableScaledResidualCubic K) y v)
      (y 1 * fderiv ℝ (fderiv ℝ (stableScaledResidualCubic K)) y v w)
    simp only [abs_mul] at H
    have H0 := mul_le_mul_of_nonneg_left (h1 w) (abs_nonneg (v 1))
    have H1 := mul_le_mul_of_nonneg_left (h1 v) (abs_nonneg (w 1))
    have H2 := mul_le_mul_of_nonneg_left (h2 v w) (abs_nonneg (y 1))
    nlinarith only [H, H0, H1, H2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_stableScaledResidual_derivative_bounds :
    ∃ C > (0 : ℝ), ∀ (c : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| ≤ 1 / 10 →
      |y 1| ≤ 1 / 100 → |y 2| ≤ 1 / 100 →
      ContDiffAt ℝ 2 (stableScaledResidual (c + 1)) y ∧
        |stableScaledResidual (c + 1) y| ≤ C / (c + 1) ^ 2 * |y 1| * (|y 1| + |y 2|) ^ 3 ∧
        (∀ v, |fderiv ℝ (stableScaledResidual (c + 1)) y v| ≤
          C / (c + 1) ^ 2 * (|v 1| * (|y 1| + |y 2|) ^ 3 + |y 1| * stableCubicFirstBudget y v)) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableScaledResidual (c + 1))) y v w| ≤
          C / (c + 1) ^ 2 * (|v 1| * stableCubicFirstBudget y w + |w 1| * stableCubicFirstBudget y v +
            |y 1| * stableCubicSecondBudget y v w)) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidualCubic_bounds
  refine ⟨C, hC, ?_⟩
  intro c y hc hm hu hw
  obtain ⟨hg, h0, h1, h2⟩ := HC c y hc hm hu hw
  exact ⟨stableScaledResidual_contDiffAt hg,
    stableScaledResidual_bounds_of_cubic hg h0 h1 h2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_stableCorrectedPhase_rescaled {c s : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    HasDerivAt (fun r => stableCorrectedPhase (stableRescaledFlow (c + 1) y r 0)
      (stableRescaledFlow (c + 1) y r 1) (stableRescaledFlow (c + 1) y r 2))
      (stableRescaledResidualRate (c + 1) s y) s := by
  have hK : 0 < c + 1 := by linarith
  have hY := stableInclusion.hasFDerivAt.comp_hasDerivAt s
    (hasDerivAt_stableRescaledFlow hK hc hm hu hw hs)
  have heq (z : StableState) : stableInclusion ((c + 1) • stableOriginalField z) =
      stableResidualClock (c + 1) z • projectiveField (stableInclusion z) := by
    rw [map_smul, stableOriginalField, map_smul, ← stableBoundaryField_inclusion, smul_smul]
    congr 1
    unfold stableResidualClock
    ring
  rw [heq] at hY
  have hM : 1 < stableInclusion (stableRescaledFlow (c + 1) y s) 0 := by
    change 1 < stableRescaledFlow (c + 1) y s 0
    have H := (abs_le.mp (stableRescaledFlow_band hc hm hu hw hs).1).1
    linarith
  have H := hasDerivAt_stableCorrectedPhase_scaled hY hM (by rfl)
  simpa [stableInclusion_apply, stableRescaledResidualRate, stableScaledResidual] using H

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_stableRescaledResidualRate_joint_two {y : StableState} {c s : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) (hs : 0 ≤ s) :
    ContDiffAt ℝ 2 (fun p : ℝ × StableState => stableRescaledResidualRate (c + 1) p.1 p.2) (s, y) := by
  obtain ⟨C, hC, HC⟩ := exists_stableScaledResidual_derivative_bounds
  obtain ⟨hM, hU, hW⟩ := stableRescaledFlow_band hc hm hu hw hs
  have hg := (HC c (stableRescaledFlow (c + 1) y s) hc hM hU hW).1
  have hp : ContDiffAt ℝ 2 (fun p : ℝ × StableState => (p.2, p.1)) (s, y) :=
    contDiffAt_snd.prodMk contDiffAt_fst
  have hflow := (contDiffAt_stableRescaledFlow_two (by linarith : 0 < c + 1) hc hm hu hw hs).comp (s, y) hp
  exact hg.comp (s, y) hflow

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exists_stableRescaledResidualRate_uniform_bounds :
    ∃ C > (0 : ℝ), ∀ (c s : ℝ) (y : StableState), 2 ≤ c → y ∈ stableParameterDomain c → 0 ≤ s →
      let B := C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s)
      |stableRescaledResidualRate (c + 1) s y| ≤ B ∧
        ‖fderiv ℝ (stableRescaledResidualRate (c + 1) s) y‖ ≤ B ∧
        ‖fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y‖ ≤ B := by
  obtain ⟨C, hC, HC⟩ := exists_stableRescaledResidualRate_weighted_decay
  refine ⟨4 * C, by positivity, ?_⟩
  intro c s y hc hy hs
  obtain ⟨_, h0, h1, h2⟩ := HC c s y hc hy.1 hy.2.1 hy.2.2 hs
  let b := |y 1| + |y 2|
  let Q := C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s)
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith [hy.2.1, hy.2.2]
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hb2 : b ^ 2 ≤ 1 := by simpa using pow_le_pow_left₀ hb hb1 2
  have hb3 : b ^ 3 ≤ 1 := by simpa using pow_le_pow_left₀ hb hb1 3
  have heq : 4 * C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s) = 4 * Q := by dsimp [Q]; ring
  dsimp only
  rw [heq]
  refine ⟨?_, ?_, ?_⟩
  · have H := mul_le_mul (show |y 1| ≤ 1 by linarith [hy.2.1]) hb3 (by positivity) (by norm_num : (0 : ℝ) ≤ 1)
    have H0 := mul_le_mul_of_nonneg_left H hQ
    dsimp only [Q, b] at H0 ⊢
    nlinarith only [h0, H0, hQ]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    have H := mul_le_mul hb3 (stableFirstInputWeight_le hb1 v)
      (stableFirstInputWeight_nonneg hb v) (by norm_num : (0 : ℝ) ≤ 1)
    have H0 := mul_le_mul_of_nonneg_left H hQ
    have Hpos := mul_nonneg hQ (norm_nonneg v)
    have R := h1 v
    simp only [Real.norm_eq_abs]
    dsimp only [Q, b] at H0 Hpos ⊢
    nlinarith only [R, H0, Hpos]
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro w
    have H := mul_le_mul (mul_le_mul hb2 (stableFirstInputWeight_le hb1 v)
      (stableFirstInputWeight_nonneg hb v) (by norm_num : (0 : ℝ) ≤ 1))
      (stableFirstInputWeight_le hb1 w) (stableFirstInputWeight_nonneg hb w) (by positivity)
    have H0 := mul_le_mul_of_nonneg_left H hQ
    have R := h2 v w
    simp only [Real.norm_eq_abs]
    dsimp only [Q, b] at H0 ⊢
    nlinarith only [R, H0]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

attribute [local instance] BianchiIX.instNormedAddCommGroupContinuousLinearMapRealIdStableState
attribute [local instance] BianchiIX.instNormedSpaceRealContinuousLinearMapIdStableState
private theorem BianchiIX.stableResidualTailIntegral_derivatives {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    IntegrableOn (fun s => fderiv ℝ (stableRescaledResidualRate (c + 1) s) y) (Ioi T) ∧
      IntegrableOn (fun s => fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y) (Ioi T) ∧
      fderiv ℝ (stableResidualTailIntegral (c + 1) T) y =
        (∫ s in Ioi T, fderiv ℝ (stableRescaledResidualRate (c + 1) s) y) ∧
      fderiv ℝ (fderiv ℝ (stableResidualTailIntegral (c + 1) T)) y =
        ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y := by
  obtain ⟨C, hC, HC⟩ := exists_stableRescaledResidualRate_uniform_bounds
  obtain ⟨A, hA, HA⟩ := exists_stableResidual_derivative_integral_tails
  have hK : 0 < c + 1 := by linarith
  let B := fun s => C / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s)
  have hB : IntegrableOn B (Ioi T) :=
    (integrableOn_exp_mul_Ioi (by linarith : -(c + 1) / 16 < 0) T).const_mul _
  exact fderiv2_integral_Ioi_of_contDiffAt
    (f := fun p : ℝ × StableState => stableRescaledResidualRate (c + 1) p.1 p.2)
    (isOpen_stableParameterDomain c) hy
    (fun z hz s hs => contDiffAt_stableRescaledResidualRate_joint_two hc hz.1.le hz.2.1.le hz.2.2.le (le_trans hT hs.le))
    (fun z hz => (HA c T z hc hz.1 hz.2.1 hz.2.2 hT).1.1) hB
    (fun z hz s hs => (HC c s z hc hz (le_trans hT hs.le)).2.1)
    (fun z hz s hs => (HC c s z hc hz (le_trans hT hs.le)).2.2)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

attribute [local instance] BianchiIX.instNormedAddCommGroupContinuousLinearMapRealIdStableState
attribute [local instance] BianchiIX.instNormedSpaceRealContinuousLinearMapIdStableState
private theorem BianchiIX.stableResidualTailIntegral_fderiv_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v : StableState) :
    fderiv ℝ (stableResidualTailIntegral (c + 1) T) y v =
      ∫ s in Ioi T, fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v := by
  have H := stableResidualTailIntegral_derivatives hc hy hT
  rw [H.2.2.1]
  exact ContinuousLinearMap.integral_apply H.1 v

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

attribute [local instance] BianchiIX.instNormedAddCommGroupContinuousLinearMapRealIdStableState
attribute [local instance] BianchiIX.instNormedSpaceRealContinuousLinearMapIdStableState
private theorem BianchiIX.stableResidualTailIntegral_fderiv2_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableResidualTailIntegral (c + 1) T)) y v w =
      ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w := by
  have H := stableResidualTailIntegral_derivatives hc hy hT
  rw [H.2.2.2, ContinuousLinearMap.integral_apply H.2.1 v]
  exact ContinuousLinearMap.integral_apply
    ((ContinuousLinearMap.apply ℝ (StableState →L[ℝ] ℝ) v).integrable_comp H.2.1) w

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableCorrectedPhaseTail_zero (K : ℝ) : stableCorrectedPhaseTail K 0 = stableCorrectedRemainder := by
  funext y
  simp only [stableCorrectedPhaseTail, stableRescaledFlow_initial, stableCorrectedRemainder]

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableResidualTailIntegral_eq_correctedPhaseTail {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    stableResidualTailIntegral (c + 1) T y = stableCorrectedPhaseTail (c + 1) T y := by
  have hK : 0 < c + 1 := by linarith
  obtain ⟨C, hC, HC⟩ := exists_stableResidual_derivative_integral_tails
  have hint := (HC c T y hc hy.1 hy.2.1 hy.2.2 hT).1.1
  have hP : 1 < stableBoundaryProjection (y 0) (y 1) (y 2) := by
    have H := (abs_le.mp (stableBoundaryProjection_band hc hy.1.le hy.2.1.le hy.2.2.le)).1
    linarith
  have hlim := (contDiffAt_stableCorrectedPhase 2
    (y := ![stableBoundaryProjection (y 0) (y 1) (y 2), 0, 0]) hP).continuousAt.tendsto.comp
      (stableRescaledFlow_limit hK hc hy.1.le hy.2.1.le hy.2.2.le)
  change Tendsto (fun s => stableCorrectedPhase (stableRescaledFlow (c + 1) y s 0)
    (stableRescaledFlow (c + 1) y s 1) (stableRescaledFlow (c + 1) y s 2)) atTop
    (𝓝 (stableCorrectedPhase (stableBoundaryProjection (y 0) (y 1) (y 2)) 0 0)) at hlim
  rw [stableCorrectedPhase_zero (by linarith)] at hlim
  exact integral_Ioi_of_hasDerivAt_of_tendsto'
    (fun s hs => hasDerivAt_stableCorrectedPhase_rescaled hc hy.1.le hy.2.1.le hy.2.2.le (le_trans hT hs))
    hint hlim

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.contDiffAt_stableCorrectedPhaseTail_two {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    ContDiffAt ℝ 2 (stableCorrectedPhaseTail (c + 1) T) y := by
  have hK : 0 < c + 1 := by linarith
  have hp : ContDiffAt ℝ 2 (fun z : StableState => (z, T)) y := contDiffAt_id.prodMk contDiffAt_const
  have hflow := (contDiffAt_stableRescaledFlow_two hK hc hy.1.le hy.2.1.le hy.2.2.le hT).comp y hp
  have hM : 1 < stableRescaledFlow (c + 1) y T 0 := by
    have H := (abs_le.mp (stableRescaledFlow_band hc hy.1.le hy.2.1.le hy.2.2.le hT).1).1
    linarith
  have hphase := (contDiffAt_stableCorrectedPhase 2 (y := stableRescaledFlow (c + 1) y T) hM).comp y hflow
  exact (contDiffAt_stableBoundaryProjection_two_in_band hc hy.1 hy.2.1 hy.2.2).sub hphase

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableResidualTailIntegral_eventually_eq {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) :
    stableResidualTailIntegral (c + 1) T =ᶠ[𝓝 y] stableCorrectedPhaseTail (c + 1) T := by
  filter_upwards [(isOpen_stableParameterDomain c).mem_nhds hy] with z hz
  exact stableResidualTailIntegral_eq_correctedPhaseTail hc hz hT

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableCorrectedPhaseTail_fderiv_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v : StableState) :
    fderiv ℝ (stableCorrectedPhaseTail (c + 1) T) y v =
      ∫ s in Ioi T, fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v := by
  rw [← (stableResidualTailIntegral_eventually_eq hc hy hT).fderiv_eq]
  exact stableResidualTailIntegral_fderiv_apply hc hy hT v

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.stableCorrectedPhaseTail_fderiv2_apply {c T : ℝ} {y : StableState}
    (hc : 2 ≤ c) (hy : y ∈ stableParameterDomain c) (hT : 0 ≤ T) (v w : StableState) :
    fderiv ℝ (fderiv ℝ (stableCorrectedPhaseTail (c + 1) T)) y v w =
      ∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w := by
  rw [← (stableResidualTailIntegral_eventually_eq hc hy hT).fderiv.fderiv_eq]
  exact stableResidualTailIntegral_fderiv2_apply hc hy hT v w

end
end

private theorem BianchiIX.exists_stableCorrectedPhaseTail_weighted_bounds :
    ∃ C > (0 : ℝ), ∀ (c T : ℝ) (y : StableState), 2 ≤ c → y ∈ stableParameterDomain c → 0 ≤ T →
      let b := |y 1| + |y 2|
      let q := Real.exp (-(c + 1) / 16 * T)
      ContDiffAt ℝ 2 (stableCorrectedPhaseTail (c + 1) T) y ∧
        |stableCorrectedPhaseTail (c + 1) T y| ≤ C / (c + 1) ^ 3 * |y 1| * b ^ 3 * q ∧
        (∀ v, |fderiv ℝ (stableCorrectedPhaseTail (c + 1) T) y v| ≤
          C / (c + 1) ^ 3 * b ^ 3 * stableFirstInputWeight b v * q) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ (stableCorrectedPhaseTail (c + 1) T)) y v w| ≤
          C / (c + 1) ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q) := by
  obtain ⟨C, hC, HC⟩ := exists_stableResidual_derivative_integral_tails
  refine ⟨C, hC, ?_⟩
  intro c T y hc hy hT
  dsimp only
  obtain ⟨h0, h1, h2⟩ := HC c T y hc hy.1 hy.2.1 hy.2.2 hT
  refine ⟨contDiffAt_stableCorrectedPhaseTail_two hc hy hT, ?_, ?_, ?_⟩
  · rw [← stableResidualTailIntegral_eq_correctedPhaseTail hc hy hT]
    exact h0.2
  · intro v
    rw [stableCorrectedPhaseTail_fderiv_apply hc hy hT]
    exact (h1 v).2
  · intro v w
    rw [stableCorrectedPhaseTail_fderiv2_apply hc hy hT]
    exact (h2 v w).2

private theorem BianchiIX.exists_stableCorrectedRemainder_weighted_bounds :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      ContDiffAt ℝ 2 stableCorrectedRemainder y ∧
        |stableCorrectedRemainder y| ≤ C / (y 0 + 1) ^ 3 * |y 1| * b ^ 3 ∧
        (∀ v, |fderiv ℝ stableCorrectedRemainder y v| ≤
          C / (y 0 + 1) ^ 3 * b ^ 3 * stableFirstInputWeight b v) ∧
        (∀ v w, |fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v w| ≤
          C / (y 0 + 1) ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w) := by
  obtain ⟨C, hC, HC⟩ := exists_stableCorrectedPhaseTail_weighted_bounds
  refine ⟨C, hC, ?_⟩
  intro y hm hu hw
  have H := HC (y 0) 0 y hm ⟨by simp, hu, hw⟩ (le_refl 0)
  simpa only [stableCorrectedPhaseTail_zero, mul_zero, Real.exp_zero, mul_one] using H


theorem solution :
    ∃ C > (0 : ℝ), ∀ y : StableState, 2 ≤ y 0 → |y 1| < 1 / 200 → |y 2| < 1 / 200 →
      let b := |y 1| + |y 2|
      let Q := C / (y 0 + 1) ^ 3
      (∀ v, |fderiv ℝ stableCorrectedRemainder y v| ≤ Q * b ^ 3 * ‖v‖) ∧
      (∀ v, v 1 = 0 → v 2 = 0 → |fderiv ℝ stableCorrectedRemainder y v| ≤ Q * b ^ 4 * ‖v‖) ∧
      (∀ v w, |fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v w| ≤ Q * b ^ 2 * ‖v‖ * ‖w‖) ∧
      (∀ v w, v 1 = 0 → v 2 = 0 →
        |fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v w| ≤ Q * b ^ 3 * ‖v‖ * ‖w‖) ∧
      (∀ v w, v 1 = 0 → v 2 = 0 → w 1 = 0 → w 2 = 0 →
        |fderiv ℝ (fderiv ℝ stableCorrectedRemainder) y v w| ≤ Q * b ^ 4 * ‖v‖ * ‖w‖) := by
  obtain ⟨C, hC, HC⟩ := exists_stableCorrectedRemainder_weighted_bounds
  refine ⟨4 * C, by positivity, ?_⟩
  intro y hm hu hw
  obtain ⟨_, _, h1, h2⟩ := HC y hm hu hw
  let b := |y 1| + |y 2|
  let Q := C / (y 0 + 1) ^ 3
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hb1 : b ≤ 1 := by dsimp [b]; linarith
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hscale : 4 * C / (y 0 + 1) ^ 3 = 4 * Q := by dsimp [Q]; ring
  dsimp only
  rw [hscale]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro v
    have R := h1 v
    have H := mul_le_mul_of_nonneg_left (stableFirstInputWeight_le hb1 v) (show 0 ≤ Q * b ^ 3 by positivity)
    have hpos : 0 ≤ Q * b ^ 3 * ‖v‖ := by positivity
    dsimp only [Q, b] at H hpos ⊢
    nlinarith only [R, H, hpos]
  · intro v hv1 hv2
    have R := h1 v
    rw [stableFirstInputWeight_center _ hv1 hv2] at R
    have hpos : 0 ≤ Q * b ^ 4 * ‖v‖ := by positivity
    dsimp only [Q, b] at hpos ⊢
    nlinarith only [R, hpos]
  · intro v w
    have R := h2 v w
    have H := mul_le_mul_of_nonneg_left
      (mul_le_mul (stableFirstInputWeight_le hb1 v) (stableFirstInputWeight_le hb1 w)
        (stableFirstInputWeight_nonneg hb w) (by positivity)) (show 0 ≤ Q * b ^ 2 by positivity)
    dsimp only [Q, b] at H ⊢
    nlinarith only [R, H]
  · intro v w hv1 hv2
    have R := h2 v w
    rw [stableFirstInputWeight_center _ hv1 hv2] at R
    have H := mul_le_mul_of_nonneg_left (stableFirstInputWeight_le hb1 w)
      (show 0 ≤ Q * b ^ 2 * (b * ‖v‖) by positivity)
    have hpos : 0 ≤ Q * b ^ 3 * ‖v‖ * ‖w‖ := by positivity
    dsimp only [Q, b] at H hpos ⊢
    nlinarith only [R, H, hpos]
  · intro v w hv1 hv2 hw1 hw2
    have R := h2 v w
    rw [stableFirstInputWeight_center _ hv1 hv2, stableFirstInputWeight_center _ hw1 hw2] at R
    have hpos : 0 ≤ Q * b ^ 4 * ‖v‖ * ‖w‖ := by positivity
    dsimp only [Q, b] at hpos ⊢
    nlinarith only [R, hpos]
