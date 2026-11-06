-- Prove2me | solution 1 for BianchiIX.exists_stableResidual_derivative_integral_tails
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T16:36:24.350368+00:00
-- url     : https://prove2.me/submissions/852ec849-72fc-48ef-ad2a-b259912ec6a3

import Definitions.Def_BianchiIX_Algebra_Flow
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Coordinates
import Definitions.Def_BianchiIX_StableProjectionRefinementData
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Algebra_MatchingPhase
import Definitions.Def_BianchiIX_CompactPhaseExpansionData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_stableRescaledResidualRate_weighted_decay
import Theorems.Thm_BianchiIX_fromProjectiveState_clock_pos
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_normalizedMaxDomain_contains_Ici_of_constraint
import Theorems.Thm_BianchiIX_normalized_stable_global_region
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

noncomputable section
open BianchiIX
open Set MeasureTheory

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
open Set MeasureTheory

private theorem BianchiIX.integrableOn_integral_tail_of_exp_bound {f : ℝ → ℝ} {K A T : ℝ}
    (hK : 0 < K) (hT : 0 ≤ T) (hf : ContinuousOn f (Ici 0))
    (hbound : ∀ s ≥ 0, |f s| ≤ A / K ^ 2 * Real.exp (-K / 16 * s)) :
    IntegrableOn f (Ioi T) ∧ |∫ s in Ioi T, f s| ≤ 16 * A / K ^ 3 * Real.exp (-K / 16 * T) := by
  have hneg : -K / 16 < 0 := by linarith
  have hg : IntegrableOn (fun s => A / K ^ 2 * Real.exp (-K / 16 * s)) (Ioi T) :=
    (integrableOn_exp_mul_Ioi hneg T).const_mul _
  have hmeas : AEStronglyMeasurable f (volume.restrict (Ioi T)) :=
    (hf.mono (fun _ hs => le_trans hT hs.le)).aestronglyMeasurable measurableSet_Ioi
  have hle : ∀ᵐ s ∂volume.restrict (Ioi T), ‖f s‖ ≤ A / K ^ 2 * Real.exp (-K / 16 * s) :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall (fun s hs => hbound s (le_trans hT hs.le)))
  refine ⟨hg.mono' hmeas hle, ?_⟩
  have H := norm_integral_le_of_norm_le hg hle
  rw [integral_const_mul, integral_exp_mul_Ioi hneg T] at H
  simp only [Real.norm_eq_abs] at H
  convert! H using 1
  field_simp

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

private theorem BianchiIX.stableBoundaryDenom_pos (y : StableState) : 0 < stableBoundaryDenom y := by
  unfold stableBoundaryDenom
  positivity

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
open Set

private theorem BianchiIX.continuousOn_stableRescaledResidualRate_derivatives {y : StableState} {c : ℝ}
    (hc : 2 ≤ c) (hm : |y 0 - c| ≤ 1 / 40)
    (hu : |y 1| ≤ 1 / 200) (hw : |y 2| ≤ 1 / 200) :
    ContinuousOn (fun s => stableRescaledResidualRate (c + 1) s y) (Ici 0) ∧
      (∀ v, ContinuousOn (fun s => fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v) (Ici 0)) ∧
      (∀ v w, ContinuousOn (fun s => fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w) (Ici 0)) := by
  have h0 (s : ℝ) (hs : 0 ≤ s) := contDiffAt_stableRescaledResidualRate_joint_two hc hm hu hw hs
  have h1 (s : ℝ) (hs : 0 ≤ s) :
      ContDiffAt ℝ 1 (fun p : ℝ × StableState => fderiv ℝ (stableRescaledResidualRate (c + 1) p.1) p.2) (s, y) :=
    contDiffAt_partial_fderiv (h0 s hs) (by norm_num)
  have h2 (s : ℝ) (hs : 0 ≤ s) :
      ContDiffAt ℝ 0 (fun p : ℝ × StableState => fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) p.1)) p.2) (s, y) :=
    contDiffAt_partial_fderiv (h1 s hs) (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    exact ((h0 s hs).continuousAt.comp (f := fun r : ℝ => (r, y))
      (continuousAt_id.prodMk continuousAt_const)).continuousWithinAt
  · intro v s hs
    exact (((h1 s hs).continuousAt.comp (f := fun r : ℝ => (r, y))
      (continuousAt_id.prodMk continuousAt_const)).clm_apply
      continuousAt_const).continuousWithinAt
  · intro v w s hs
    exact ((((h2 s hs).continuousAt.comp (f := fun r : ℝ => (r, y))
      (continuousAt_id.prodMk continuousAt_const)).clm_apply
      continuousAt_const).clm_apply continuousAt_const).continuousWithinAt

end
end

theorem solution :
    ∃ C > (0 : ℝ), ∀ (c T : ℝ) (y : StableState), 2 ≤ c → |y 0 - c| < 1 / 40 →
      |y 1| < 1 / 200 → |y 2| < 1 / 200 → 0 ≤ T →
      let b := |y 1| + |y 2|
      let q := Real.exp (-(c + 1) / 16 * T)
      (IntegrableOn (fun s => stableRescaledResidualRate (c + 1) s y) (Ioi T) ∧
        |∫ s in Ioi T, stableRescaledResidualRate (c + 1) s y| ≤
          C / (c + 1) ^ 3 * |y 1| * b ^ 3 * q) ∧
      (∀ v, IntegrableOn (fun s => fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v) (Ioi T) ∧
        |∫ s in Ioi T, fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v| ≤
          C / (c + 1) ^ 3 * b ^ 3 * stableFirstInputWeight b v * q) ∧
      (∀ v w, IntegrableOn (fun s => fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w) (Ioi T) ∧
        |∫ s in Ioi T, fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w| ≤
          C / (c + 1) ^ 3 * b ^ 2 * stableFirstInputWeight b v * stableFirstInputWeight b w * q) := by
  obtain ⟨C, hC, HC⟩ := exists_stableRescaledResidualRate_weighted_decay
  refine ⟨16 * C, by positivity, ?_⟩
  intro c T y hc hm hu hw hT
  dsimp only
  have hK : 0 < c + 1 := by linarith
  obtain ⟨hcont0, hcont1, hcont2⟩ := continuousOn_stableRescaledResidualRate_derivatives hc hm.le hu.le hw.le
  refine ⟨?_, ?_, ?_⟩
  · have hbound (s : ℝ) (hs : 0 ≤ s) :
        |stableRescaledResidualRate (c + 1) s y| ≤
          (C * |y 1| * (|y 1| + |y 2|) ^ 3) / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s) := by
      convert! (HC c s y hc hm hu hw hs).2.1 using 1
      ring
    obtain ⟨hi, H⟩ := integrableOn_integral_tail_of_exp_bound hK hT hcont0 hbound
    refine ⟨hi, ?_⟩
    convert! H using 1
    ring
  · intro v
    have hbound (s : ℝ) (hs : 0 ≤ s) :
        |fderiv ℝ (stableRescaledResidualRate (c + 1) s) y v| ≤
          (C * (|y 1| + |y 2|) ^ 3 * stableFirstInputWeight (|y 1| + |y 2|) v) / (c + 1) ^ 2 *
            Real.exp (-(c + 1) / 16 * s) := by
      convert! (HC c s y hc hm hu hw hs).2.2.1 v using 1
      ring
    obtain ⟨hi, H⟩ := integrableOn_integral_tail_of_exp_bound hK hT (hcont1 v) hbound
    refine ⟨hi, ?_⟩
    convert! H using 1
    ring
  · intro v w
    have hbound (s : ℝ) (hs : 0 ≤ s) :
        |fderiv ℝ (fderiv ℝ (stableRescaledResidualRate (c + 1) s)) y v w| ≤
          (C * (|y 1| + |y 2|) ^ 2 * stableFirstInputWeight (|y 1| + |y 2|) v *
            stableFirstInputWeight (|y 1| + |y 2|) w) / (c + 1) ^ 2 * Real.exp (-(c + 1) / 16 * s) := by
      convert! (HC c s y hc hm hu hw hs).2.2.2 v w using 1
      ring
    obtain ⟨hi, H⟩ := integrableOn_integral_tail_of_exp_bound hK hT (hcont2 v w) hbound
    refine ⟨hi, ?_⟩
    convert! H using 1
    ring
