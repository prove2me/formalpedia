-- Prove2me | solution 1 for BianchiIX.exists_terminal_exitReturn_radial_bounds_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:23:07.593982+00:00
-- url     : https://prove2.me/submissions/4bfafbfc-373f-40fd-ae78-89f95c5ef7c1

import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreTailValid_of_height_le
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_exists_exitTail_scale_bounds
import Theorems.Thm_BianchiIX_exists_scalar_event_branch_two
import Theorems.Thm_BianchiIX_exists_terminal_exitClock_multiplier_bounds
import Theorems.Thm_BianchiIX_exitClock_radial_column_bound
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toExitTailState
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projective_inverse_scale
import Theorems.Thm_BianchiIX_toProjectiveState_fromProjectiveState
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
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Tactic.GCongr
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Order.OrderClosed
import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Topology.MetricSpace.Thickening
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Topology.Instances.Matrix
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Topology.Algebra.Module.Determinant
import Mathlib.Analysis.Calculus.Deriv.Pi
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

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

private theorem BianchiIX.exp_neg_exitTailLength {η α : ℝ} (hη : 0 < η) (hα : 0 < α) (J : ℕ) :
    Real.exp (-exitTailLength η α J) = η * α ^ J := by
  simp only [exitTailLength, one_div, Real.log_inv]
  rw [show -(-Real.log η + (J : ℝ) * -Real.log α) = Real.log η + J * Real.log α by ring,
    Real.exp_add, Real.exp_nat_mul, Real.exp_log hη, Real.exp_log hα]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailLength_nonneg {η α : ℝ} (hη : 0 < η ∧ η ≤ 1) (hα : 0 < α ∧ α ≤ 1) (J : ℕ) :
    0 ≤ exitTailLength η α J := by
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have ha : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((le_div_iff₀ hα.1).mpr (by linarith only [hα.2]))
  exact add_nonneg he (mul_nonneg (Nat.cast_nonneg _) ha)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.power_mul_log_inv_bound {α : ℝ} (hα : 0 < α) (J : ℕ) :
    α ^ J * ((J : ℝ) * Real.log (1 / α)) ≤ Real.exp (-1) := by
  have H := Real.mul_exp_neg_le_exp_neg_one ((J : ℝ) * Real.log (1 / α))
  have he : Real.exp (-((J : ℝ) * Real.log (1 / α))) = α ^ J := by
    rw [one_div, Real.log_inv, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hα]
  rw [he] at H
  linarith only [H]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.sq_mul_exp_neg_bound {x : ℝ} (hx : 0 ≤ x) :
    x ^ 2 * Real.exp (-x) ≤ 4 * Real.exp (-2) := by
  have H := Real.mul_exp_neg_le_exp_neg_one (x / 2)
  have hpos : 0 ≤ x / 2 * Real.exp (-(x / 2)) := mul_nonneg (by positivity) (Real.exp_pos _).le
  have Hsq := (sq_le_sq₀ hpos (Real.exp_pos _).le).mpr H
  have h1 : Real.exp (-(x / 2)) ^ 2 = Real.exp (-x) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have h2 : Real.exp (-1) ^ 2 = Real.exp (-2) := by rw [sq, ← Real.exp_add]; norm_num
  rw [mul_pow, h1, h2] at Hsq
  nlinarith only [Hsq]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailLength_weighted_bounds {η α : ℝ} (hη : 0 < η ∧ η ≤ 1)
    (hα : 0 < α ∧ α ≤ 1) (J : ℕ) :
    α * exitTailLength η α J ≤ Real.log (1 / η) + J * Real.exp (-1) ∧
    α ^ J * (1 + exitTailLength η α J) ≤ 1 + Real.log (1 / η) + Real.exp (-1) ∧
    α ^ J * (1 + exitTailLength η α J) ^ 2 ≤
      2 * (1 + Real.log (1 / η)) ^ 2 + 8 * Real.exp (-2) := by
  have he : 0 ≤ Real.log (1 / η) := Real.log_nonneg ((le_div_iff₀ hη.1).mpr (by linarith only [hη.2]))
  have ha : 0 ≤ Real.log (1 / α) := Real.log_nonneg ((le_div_iff₀ hα.1).mpr (by linarith only [hα.2]))
  have hp0 := pow_nonneg hα.1.le J
  have hp1 : α ^ J ≤ 1 := pow_le_one₀ hα.1.le hα.2
  have H1 := power_mul_log_inv_bound hα.1 1
  simp only [pow_one, Nat.cast_one, one_mul] at H1
  have HJ := power_mul_log_inv_bound hα.1 J
  have Hsq := sq_mul_exp_neg_bound (mul_nonneg (Nat.cast_nonneg J) ha)
  have hExp : Real.exp (-((J : ℝ) * Real.log (1 / α))) = α ^ J := by
    rw [one_div, Real.log_inv, mul_neg, neg_neg, Real.exp_nat_mul, Real.exp_log hα.1]
  rw [hExp] at Hsq
  refine ⟨?_, ?_, ?_⟩
  · dsimp only [exitTailLength]
    nlinarith only [mul_le_mul_of_nonneg_right hα.2 he,
      mul_le_mul_of_nonneg_left H1 (Nat.cast_nonneg J)]
  · dsimp only [exitTailLength]
    nlinarith only [HJ, mul_le_mul_of_nonneg_right hp1 (by positivity : 0 ≤ 1 + Real.log (1 / η))]
  · have Hsplit : (1 + exitTailLength η α J) ^ 2 ≤
        2 * (1 + Real.log (1 / η)) ^ 2 + 2 * ((J : ℝ) * Real.log (1 / α)) ^ 2 := by
      dsimp only [exitTailLength]
      nlinarith only [sq_nonneg (1 + Real.log (1 / η) - J * Real.log (1 / α))]
    have H := mul_le_mul_of_nonneg_left Hsplit hp0
    have HB := mul_le_mul_of_nonneg_right hp1 (sq_nonneg (1 + Real.log (1 / η)))
    nlinarith only [H, HB, Hsq]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.intervalScalarInverse_eq {E : Type*} {Q : E × ℝ → ℝ} {I : Set ℝ}
    {x : E} {s t : ℝ} (hm : StrictMonoOn (fun r => Q (x, r)) I)
    (ht : t ∈ I) (he : Q (x, t) = s) : intervalScalarInverse Q I (x, s) = t := by
  have h : ∃ r ∈ I, Q (x, r) = s := ⟨t, ht, he⟩
  rw [intervalScalarInverse, dif_pos h]
  exact hm.injOn (Classical.choose_spec h).1 ht ((Classical.choose_spec h).2.trans he.symm)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem BianchiIX.intervalScalarInverse_regular {Q : E × ℝ → ℝ} {I : Set ℝ} {x : E} {t a : ℝ}
    (hI : IsOpen I) (ht : t ∈ I) (hQ : ContDiffAt ℝ 2 Q (x, t))
    (hd : HasDerivAt (fun r => Q (x, r)) a t) (ha : a ≠ 0)
    (hm : ∀ᶠ z in 𝓝 x, StrictMonoOn (fun r => Q (z, r)) I) :
    ContDiffAt ℝ 2 (intervalScalarInverse Q I) (x, Q (x, t)) ∧
      (∀ᶠ p in 𝓝 (x, Q (x, t)), intervalScalarInverse Q I p ∈ I ∧
        Q (p.1, intervalScalarInverse Q I p) = p.2) := by
  let F : (E × ℝ) × ℝ → ℝ := fun p => Q (p.1.1, p.2) - p.1.2
  have hmap : ContDiffAt ℝ 2 (fun p : (E × ℝ) × ℝ => (p.1.1, p.2)) ((x, Q (x, t)), t) := by fun_prop
  have hF : ContDiffAt ℝ 2 F ((x, Q (x, t)), t) := by
    have H := hQ.comp ((x, Q (x, t)), t) hmap
    exact H.sub (by fun_prop)
  have hFd : HasDerivAt (fun r => F ((x, Q (x, t)), r)) a t := hd.sub_const _
  obtain ⟨τ, hτ, hcτ, _, hhit, _⟩ := exists_scalar_event_branch_two hF hFd ha
  have hm' : ∀ᶠ p : E × ℝ in 𝓝 (x, Q (x, t)), StrictMonoOn (fun r => Q (p.1, r)) I :=
    (show ContinuousAt (fun p : E × ℝ => p.1) (x, Q (x, t)) from continuousAt_fst).eventually hm
  have hτI : ∀ᶠ p in 𝓝 (x, Q (x, t)), τ p ∈ I :=
    hcτ.continuousAt.eventually (hI.mem_nhds (hτ.symm ▸ ht))
  have hnear : ∀ᶠ p in 𝓝 (x, Q (x, t)), intervalScalarInverse Q I p = τ p ∧
      τ p ∈ I ∧ Q (p.1, τ p) = p.2 := by
    filter_upwards [hm', hτI, hhit] with p hmp hIp hp
    have he : Q (p.1, τ p) = p.2 := by
      change Q (p.1, τ p) - p.2 = Q (x, t) - Q (x, t) at hp
      linarith only [hp]
    exact ⟨intervalScalarInverse_eq hmp hIp he, hIp, he⟩
  refine ⟨hcτ.congr_of_eventuallyEq (hnear.mono fun _ h => h.1), ?_⟩
  filter_upwards [hnear] with p hp
  simpa only [hp.1] using hp.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

private theorem BianchiIX.hasDerivAt_intervalScalarInverse_clock {Q : E × ℝ → ℝ} {I : Set ℝ} {x : E} {t a : ℝ}
    (hI : IsOpen I) (ht : t ∈ I) (hQ : ContDiffAt ℝ 2 Q (x, t))
    (hd : HasDerivAt (fun r => Q (x, r)) a t) (ha : a ≠ 0)
    (hm : ∀ᶠ z in 𝓝 x, StrictMonoOn (fun r => Q (z, r)) I) :
    HasDerivAt (fun s => intervalScalarInverse Q I (x, s)) (1 / a) (Q (x, t)) := by
  obtain ⟨hc, hnear⟩ := intervalScalarInverse_regular hI ht hQ hd ha hm
  have he := intervalScalarInverse_eq hm.self_of_nhds ht rfl
  have hslice : ContDiffAt ℝ 2 (fun s => intervalScalarInverse Q I (x, s)) (Q (x, t)) :=
    hc.comp (Q (x, t)) (contDiffAt_const.prodMk contDiffAt_id)
  have Hτ := (hslice.differentiableAt (by norm_num)).hasDerivAt
  have Hcomp := hd.comp_of_eq (Q (x, t)) Hτ he.symm
  have heq : (fun s => Q (x, intervalScalarInverse Q I (x, s))) =ᶠ[𝓝 (Q (x, t))] id := by
    have H := (continuousAt_const.prodMk continuousAt_id).eventually hnear
    filter_upwards [H] with s hs
    exact hs.2
  have Hscalar := (Hcomp.congr_of_eventuallyEq heq.symm).unique (hasDerivAt_id _)
  have Hval : deriv (fun s => intervalScalarInverse Q I (x, s)) (Q (x, t)) = 1 / a := by
    apply (eq_div_iff ha).mpr
    linarith only [Hscalar]
  rwa [Hval] at Hτ

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.hasDerivAt_parametric_first_variation {Φ : E × ℝ → F} {f : ℝ × F → F} {x : E} {t : ℝ}
    (hΦ : ContDiffAt ℝ 2 Φ (x, t)) (hf : DifferentiableAt ℝ f (t, Φ (x, t)))
    (hode : (fun p => fderiv ℝ Φ p (0, 1)) =ᶠ[𝓝 (x, t)] (fun p => f (p.2, Φ p))) (v : E) :
    HasDerivAt (fun s => fderiv ℝ Φ (x, s) (v, 0))
      (fderiv ℝ (fun z => f (t, z)) (Φ (x, t)) (fderiv ℝ Φ (x, t) (v, 0))) t := by
  have hD := (hΦ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hleft := hD.hasFDerivAt.clm_apply (hasFDerivAt_const (0, 1) (x, t))
  have hright := hf.hasFDerivAt.comp (x, t)
    (hasFDerivAt_snd.prodMk (hΦ.differentiableAt (by norm_num)).hasFDerivAt)
  have heq := congrArg (fun L : (E × ℝ) →L[ℝ] F => L (v, 0))
    ((hleft.congr_of_eventuallyEq hode.symm).unique hright)
  have hslice := hf.hasFDerivAt.comp (Φ (x, t))
    ((hasFDerivAt_const t (Φ (x, t))).prodMk (hasFDerivAt_id (Φ (x, t))))
  change HasFDerivAt (fun z => f (t, z)) _ (Φ (x, t)) at hslice
  have hpath : HasDerivAt (fun s : ℝ => (x, s)) (0, 1) t :=
    (hasDerivAt_const t x).prodMk (hasDerivAt_id t)
  have H := hasDerivAt_fderiv_apply_const hD hpath (v, 0)
  apply H.congr_deriv
  rw [(hΦ.isSymmSndFDerivAt (by norm_num)).eq (0, 1) (v, 0), hslice.fderiv]
  simpa using heq

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

private theorem BianchiIX.coreRadius_pos {m v : ℝ} (hv : 0 < v) : 0 < coreRadius m v := by
  apply Real.sqrt_pos.mpr
  unfold coreEnergy
  positivity

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_of_coreRadius {m v : ℝ} (hm : m < 1) :
    exitTailGap (coreRadius m v) v = 1 - m := by
  unfold exitTailGap
  rw [coreRadius_sq]
  dsimp only [coreEnergy]
  rw [add_sub_cancel_right, Real.sqrt_sq_eq_abs, abs_of_neg (by linarith only [hm] : m - 1 < 0)]
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_projectiveCoreRadius (n : WithTop ℕ∞) {y : ProjectiveState}
    (hv : 0 < y 2) : ContDiffAt ℝ n (fun z : ProjectiveState => coreRadius (z 0) (z 2)) y := by
  have he : coreEnergy (y 0) (y 2) ≠ 0 := by unfold coreEnergy; positivity
  have he' : (y 0 - 1) ^ 2 + y 2 ^ 2 ≠ 0 := he
  unfold coreRadius coreEnergy
  fun_prop

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

private theorem BianchiIX.projectiveOriginalFlow_initial {y : ProjectiveState} (hD : 0 < projectiveStateDenom y) (t₀ : ℝ) :
    projectiveOriginalFlow y t₀ t₀ = y := by
  rw [projectiveOriginalFlow, normalizedMaxCurve_initial]
  exact toProjectiveState_fromProjectiveState (ne_of_gt hD)

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
open Set

private theorem BianchiIX.hasDerivAt_exitLog_scaled {β : ℝ → ProjectiveState} {a t : ℝ}
    (hβ : HasDerivAt β (a • projectiveField (β t)) t) (hv : β t 2 ≠ 0) :
    HasDerivAt (fun s => -Real.log (β s 2)) (a * exitClockRate (β t)) t := by
  have H := ((hasDerivAt_pi.mp hβ 2).log hv).neg
  convert! H using 1
  change a * exitClockRate (β t) = -(a * activeVelocity (β t 0) (β t 1) (β t 2) (β t 3) / β t 2)
  dsimp [exitClockRate, activeVelocity]
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exitClockRate_tail {y : ProjectiveState} (hm : y 0 < 1) :
    exitClockRate y = exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) := by
  dsimp only [exitClockRate, exitTailSpeed]
  rw [exitTailGap_of_coreRadius hm]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_exitTailField (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hR : Y 0 ≠ 0)
    (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailField q.1 q.2) (v, Y) := by
  have hcoord (i : Fin 3) : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => q.2 i) (v, Y) := by fun_prop
  have hgap : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailGap (q.2 0) q.1) (v, Y) := by
    unfold exitTailGap
    exact (((hcoord 0).pow 2).sub (contDiffAt_fst.pow 2)).sqrt
      (ne_of_gt (sub_pos.mpr hv))
  have hc : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => coupling (q.2 1) q.1 (q.2 2)) (v, Y) := by
    unfold coupling
    fun_prop
  have hs : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailSpeed (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y) := hgap.add hc
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailRadial (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y)
    unfold exitTailRadial
    exact (((hc.neg.mul (hcoord 0)).sub
      ((hgap.mul (by fun_prop)).div (by fun_prop) hR)).div hs hd)
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailStrongRate (q.2 0) (q.2 1) q.1 (q.2 2) * q.2 1) (v, Y)
    unfold exitTailStrongRate
    apply ContDiffAt.mul _ (hcoord 1)
    have hn : ContDiffAt ℝ n (fun q : ℝ × ExitTailState =>
        2 * exitTailGap (q.2 0) q.1 - (q.2 0) ^ 2 + 2 * q.1 * q.2 2 - (q.2 2) ^ 2 + (q.2 1) ^ 2) (v, Y) := by fun_prop
    exact hn.div (contDiffAt_const.mul hs) (mul_ne_zero (by norm_num) hd)
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailWeakRate (q.2 0) (q.2 1) q.1 (q.2 2) * q.2 2) (v, Y)
    unfold exitTailWeakRate
    apply ContDiffAt.mul _ (hcoord 2)
    exact ((hgap.sub contDiffAt_const).sub hc).div hs hd

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_exitLogClock (n : WithTop ℕ∞) {y : ProjectiveState} (hv : 0 < y 2) :
    ContDiffAt ℝ n exitLogClock y := by
  unfold exitLogClock
  have H : ContDiffAt ℝ n (fun z : ProjectiveState => z 2) y := by fun_prop
  exact (H.log hv.ne').neg

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_toExitTailState (n : WithTop ℕ∞) {y : ProjectiveState} (hv : 0 < y 2) :
    ContDiffAt ℝ n toExitTailState y := by
  have hr := contDiffAt_projectiveCoreRadius n hv
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · exact hr
  · change ContDiffAt ℝ n (fun z : ProjectiveState => z 1) y
    fun_prop
  · change ContDiffAt ℝ n (fun z : ProjectiveState => z 3) y
    fun_prop

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exp_neg_exitLogClock {y : ProjectiveState} (hv : 0 < y 2) :
    Real.exp (-exitLogClock y) = y 2 := by simp [exitLogClock, Real.exp_log hv]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitLogClock_fderiv_field {y : ProjectiveState} (hv : 0 < y 2) :
    fderiv ℝ exitLogClock y (projectiveOriginalField y) = exitOriginalClockRate y := by
  let β : ℝ → ProjectiveState := fun s => y + s • projectiveOriginalField y
  have hzero : β 0 = y := by simp [β]
  have hβ : HasDerivAt β (projectiveOriginalField (β 0)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (projectiveOriginalField y)) using 1
    simp [hzero]
  have hp := ((contDiffAt_exitLogClock 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have H := hp.comp_hasDerivAt_of_eq 0 hβ hzero.symm
  have H' := hasDerivAt_exitLog_scaled hβ (by simpa only [hzero] using hv.ne')
  simpa only [hzero, exitLogClock, exitOriginalClockRate] using H.unique H'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.toExitTailState_fderiv_exitLogField {y : ProjectiveState}
    (hv : 0 < y 2) (hm : y 0 < 1) :
    fderiv ℝ toExitTailState y (exitLogField y) = exitTailField (y 2) (toExitTailState y) := by
  let β : ℝ → ProjectiveState := fun s => y + s • exitLogField y
  have hzero : β 0 = y := by simp [β]
  have hβ : HasDerivAt β (exitLogField (β 0)) 0 := by
    convert! (hasDerivAt_const (0 : ℝ) y).add
      ((hasDerivAt_id (0 : ℝ)).smul_const (exitLogField y)) using 1
    simp [hzero]
  have hp := ((contDiffAt_toExitTailState 1 hv).differentiableAt (by norm_num)).hasFDerivAt
  have H := hp.comp_hasDerivAt_of_eq 0 hβ hzero.symm
  have H' := hasDerivAt_toExitTailState hβ (hzero.symm ▸ hv) (hzero.symm ▸ hm)
  simpa only [hzero] using H.unique H'

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.toExitTailState_fderiv_field {y : ProjectiveState}
    (hv : 0 < y 2) (hm : y 0 < 1) (hd : exitClockRate y ≠ 0) :
    fderiv ℝ toExitTailState y (projectiveOriginalField y) =
      exitOriginalClockRate y • exitTailField (y 2) (toExitTailState y) := by
  have heq : projectiveOriginalField y = exitOriginalClockRate y • exitLogField y := by
    simp only [projectiveOriginalField, exitOriginalClockRate, exitLogField, smul_smul]
    rw [mul_assoc, mul_inv_cancel₀ hd, mul_one]
  rw [heq, map_smul, toExitTailState_fderiv_exitLogField hv hm]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitOriginalClockRate_normalized {y : ProjectiveState} {t₀ t : ℝ}
    (hD : 0 < projectiveStateDenom y) (ht : t ∈ normalizedMaxDomain (fromProjectiveState y) t₀)
    (hA : 0 < 1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) :
    exitOriginalClockRate (projectiveOriginalFlow y t₀ t) =
      (1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0) *
        exitClockRate (projectiveOriginalFlow y t₀ t) := by
  have hc : stateConstraint (normalizedMaxCurve (fromProjectiveState y) t₀ t) = 1 :=
    (normalizedMaxCurve_constraint ht).trans (fromProjectiveState_constraint hD.ne')
  unfold exitOriginalClockRate
  rw [show 6 / projectiveStateDenom (projectiveOriginalFlow y t₀ t) =
    1 + normalizedMaxCurve (fromProjectiveState y) t₀ t 0 from projective_inverse_scale hA.ne' hc]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_coreTailEntry (n : WithTop ℕ∞) {Y : CoreAngleState} (hk : 1 < Y 0) :
    ContDiffAt ℝ n coreTailEntry Y := by
  have hs : Y 0 ^ 2 - 1 ≠ 0 := ne_of_gt (by nlinarith only [hk] : 0 < Y 0 ^ 2 - 1)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [coreTailEntry] <;> fun_prop

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.coreTailState_active {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    coreTailState η Y 2 = η := hvalid.1.1.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_exitEntryFlow_two {Y : ExitTailState} {t : ℝ} (H : exitEntryRegular Y t) :
    ContDiffAt ℝ 2 exitEntryFlow (Y, t) := by
  have hmap : ContDiffAt ℝ 2 (fun p : ExitTailState × ℝ => (coreTailEntry p.1, p.2)) (Y, t) :=
    ((contDiffAt_coreTailEntry 2 H.1).comp (Y, t) contDiffAt_fst).prodMk contDiffAt_snd
  have HF := (contDiffAt_projectiveOriginalFlow_two H.2.1 H.2.2.1 H.2.2.2.1).comp (Y, t) hmap
  exact HF

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_exitEntryClock_two {Y : ExitTailState} {t : ℝ} (H : exitEntryRegular Y t) :
    ContDiffAt ℝ 2 exitEntryClock (Y, t) :=
  (contDiffAt_exitLogClock 2 H.2.2.2.2.1).comp (Y, t) (contDiffAt_exitEntryFlow_two H)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_exitEntryClock {Y : ExitTailState} {t : ℝ} (H : exitEntryRegular Y t) :
    HasDerivAt (fun r => exitEntryClock (Y, r)) (exitOriginalClockRate (exitEntryFlow (Y, t))) t := by
  have hflow := hasDerivAt_projectiveOriginalFlow_time H.2.1 H.2.2.1 H.2.2.2.1
  have hclock := ((contDiffAt_exitLogClock 1 H.2.2.2.2.1).differentiableAt (by norm_num)).hasFDerivAt
  have HC := hclock.comp_hasDerivAt t hflow
  change HasDerivAt (fun r => exitEntryClock (Y, r))
    (fderiv ℝ exitLogClock (exitEntryFlow (Y, t)) (projectiveOriginalField (exitEntryFlow (Y, t)))) t at HC
  rwa [exitLogClock_fderiv_field H.2.2.2.2.1] at HC

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitEntryRegular_rate_pos {Y : ExitTailState} {t : ℝ} (H : exitEntryRegular Y t) :
    0 < exitOriginalClockRate (exitEntryFlow (Y, t)) := by
  change 0 < exitOriginalClockRate (projectiveOriginalFlow (coreTailEntry Y) 0 t)
  rw [exitOriginalClockRate_normalized H.2.1 H.2.2.1 H.2.2.2.1]
  exact mul_pos H.2.2.2.1 H.2.2.2.2.2.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitEntryClock_strictMonoOn {Y : ExitTailState} {I : Set ℝ}
    (hI : Convex ℝ I) (H : ∀ t ∈ I, exitEntryRegular Y t) :
    StrictMonoOn (fun t => exitEntryClock (Y, t)) I := by
  apply strictMonoOn_of_deriv_pos hI (HasDerivAt.continuousOn (fun t ht => hasDerivAt_exitEntryClock (H t ht)))
  intro t ht
  rw [(hasDerivAt_exitEntryClock (H t (interior_subset ht))).deriv]
  exact exitEntryRegular_rate_pos (H t (interior_subset ht))

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockTime_eq {I : Set ℝ} (hI : Convex ℝ I) {Y : ExitTailState} {t : ℝ}
    (H : ∀ r ∈ I, exitEntryRegular Y r) (ht : t ∈ I) :
    exitClockTime I (Y, exitEntryClock (Y, t)) = t :=
  intervalScalarInverse_eq (exitEntryClock_strictMonoOn hI H) ht rfl

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockFlow_eq {I : Set ℝ} (hI : Convex ℝ I) {Y : ExitTailState} {t : ℝ}
    (H : ∀ r ∈ I, exitEntryRegular Y r) (ht : t ∈ I) :
    exitClockFlow I (Y, exitEntryClock (Y, t)) = toExitTailState (exitEntryFlow (Y, t)) := by
  simp only [exitClockFlow, exitClockTime_eq hI H ht]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitEntryClock_initial {Y : ExitTailState} (hD : 0 < projectiveStateDenom (coreTailEntry Y)) :
    exitEntryClock (Y, 0) = 0 := by
  change exitLogClock (projectiveOriginalFlow (coreTailEntry Y) 0 0) = 0
  rw [projectiveOriginalFlow_initial hD]
  simp [exitLogClock, coreTailEntry]

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockTime_regular {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {Y : ExitTailState} {t : ℝ} (ht : t ∈ I)
    (H : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r) :
    ContDiffAt ℝ 2 (exitClockTime I) (Y, exitEntryClock (Y, t)) ∧
      (∀ᶠ p in 𝓝 (Y, exitEntryClock (Y, t)), exitClockTime I p ∈ I ∧
        exitEntryClock (p.1, exitClockTime I p) = p.2) := by
  have HR := H.self_of_nhds t ht
  exact intervalScalarInverse_regular hIo ht (contDiffAt_exitEntryClock_two HR)
    (hasDerivAt_exitEntryClock HR) (exitEntryRegular_rate_pos HR).ne'
    (H.mono fun _ h => exitEntryClock_strictMonoOn hI h)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_exitClockFlow_two {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {Y : ExitTailState} {t : ℝ} (ht : t ∈ I)
    (H : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r) :
    ContDiffAt ℝ 2 (exitClockFlow I) (Y, exitEntryClock (Y, t)) := by
  have HR := H.self_of_nhds t ht
  have Hτ := (exitClockTime_regular hIo hI ht H).1
  have he := exitClockTime_eq hI H.self_of_nhds ht
  have hF : ContDiffAt ℝ 2 exitEntryFlow (Y, exitClockTime I (Y, exitEntryClock (Y, t))) := by
    rw [he]
    exact contDiffAt_exitEntryFlow_two HR
  have HF := hF.comp (Y, exitEntryClock (Y, t)) (contDiffAt_fst.prodMk Hτ)
  have hp : ContDiffAt ℝ 2 toExitTailState
      (exitEntryFlow (Y, exitClockTime I (Y, exitEntryClock (Y, t)))) := by
    rw [he]
    exact contDiffAt_toExitTailState 2 HR.2.2.2.2.1
  exact hp.comp (Y, exitEntryClock (Y, t)) HF

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_exitClockFlow_time {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {Y : ExitTailState} {t : ℝ} (ht : t ∈ I)
    (H : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r) :
    HasDerivAt (fun s => exitClockFlow I (Y, s))
      (exitTailField (Real.exp (-exitEntryClock (Y, t)))
        (exitClockFlow I (Y, exitEntryClock (Y, t)))) (exitEntryClock (Y, t)) := by
  have HR := H.self_of_nhds t ht
  have he := exitClockTime_eq hI H.self_of_nhds ht
  have Hτ := hasDerivAt_intervalScalarInverse_clock hIo ht (contDiffAt_exitEntryClock_two HR)
    (hasDerivAt_exitEntryClock HR) (exitEntryRegular_rate_pos HR).ne'
    (H.mono fun _ h => exitEntryClock_strictMonoOn hI h)
  change HasDerivAt (fun s => exitClockTime I (Y, s)) _ _ at Hτ
  have hF := hasDerivAt_projectiveOriginalFlow_time HR.2.1 HR.2.2.1 HR.2.2.2.1
  have hFc : HasDerivAt (fun r => exitEntryFlow (Y, r)) (projectiveOriginalField (exitEntryFlow (Y, t)))
      (exitClockTime I (Y, exitEntryClock (Y, t))) := by rw [he]; exact hF
  have hp := ((contDiffAt_toExitTailState 1 HR.2.2.2.2.1).differentiableAt (by norm_num)).hasFDerivAt
  have hp' : HasFDerivAt toExitTailState (fderiv ℝ toExitTailState (exitEntryFlow (Y, t)))
      (exitEntryFlow (Y, exitClockTime I (Y, exitEntryClock (Y, t)))) := by rw [he]; exact hp
  have HC := hFc.scomp (h := fun s => exitClockTime I (Y, s)) (exitEntryClock (Y, t)) Hτ
  have HO := hp'.comp_hasDerivAt (exitEntryClock (Y, t)) HC
  change HasDerivAt (fun s => exitClockFlow I (Y, s))
    (fderiv ℝ toExitTailState (exitEntryFlow (Y, t))
      ((1 / exitOriginalClockRate (exitEntryFlow (Y, t))) • projectiveOriginalField (exitEntryFlow (Y, t)))) _ at HO
  rw [map_smul, toExitTailState_fderiv_field HR.2.2.2.2.1 HR.2.2.2.2.2.1 HR.2.2.2.2.2.2.ne',
    smul_smul, one_div, inv_mul_cancel₀ (exitEntryRegular_rate_pos HR).ne', one_smul] at HO
  rw [exitClockFlow_eq hI H.self_of_nhds ht]
  simpa only [exitEntryClock, exp_neg_exitLogClock HR.2.2.2.2.1] using HO

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockFlow_local_ode {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {t : ℝ} (ht : t ∈ I) :
    ∀ᶠ p in 𝓝 (Y, exitEntryClock (Y, t)),
      ContDiffAt ℝ 2 (exitClockFlow I) p ∧
      HasDerivAt (fun s => exitClockFlow I (p.1, s))
        (exitTailField (Real.exp (-p.2)) (exitClockFlow I p)) p.2 := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have Hp := (show ContinuousAt (fun p : ExitTailState × ℝ => p.1)
    (Y, exitEntryClock (Y, t)) from continuousAt_fst).eventually (hUo.mem_nhds hY)
  filter_upwards [(exitClockTime_regular hIo hI ht HY).2, Hp] with p hp hpu
  have HZ : ∀ᶠ Z in 𝓝 p.1, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hpu] with Z hZ
    exact H Z hZ
  have HR := contDiffAt_exitClockFlow_two hIo hI hp.1 HZ
  have HD := hasDerivAt_exitClockFlow_time hIo hI hp.1 HZ
  rw [hp.2] at HR HD
  exact ⟨HR, HD⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockFlow_local_partial_time {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {t : ℝ} (ht : t ∈ I) :
    (fun p => fderiv ℝ (exitClockFlow I) p (0, 1)) =ᶠ[𝓝 (Y, exitEntryClock (Y, t))]
      (fun p => exitTailField (Real.exp (-p.2)) (exitClockFlow I p)) := by
  filter_upwards [exitClockFlow_local_ode hIo hI hUo hY H ht] with p hp
  have hpath : HasDerivAt (fun s : ℝ => (p.1, s)) (0, 1) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have HD := (hp.1.differentiableAt (by norm_num)).hasFDerivAt.comp_hasDerivAt
    (f := fun s : ℝ => (p.1, s)) p.2 hpath
  exact HD.unique hp.2

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_exitClockField {y : ProjectiveState} (hV : 0 < y 2) (hm : y 0 < 1)
    (hd : exitClockRate y ≠ 0) (n : ℕ) :
    ContDiffAt ℝ n (fun p : ℝ × ExitTailState => exitTailField (Real.exp (-p.1)) p.2)
      (exitLogClock y, toExitTailState y) := by
  have hrad := coreRadius_pos (m := y 0) hV
  have hvR : (y 2) ^ 2 < coreRadius (y 0) (y 2) ^ 2 := by
    rw [coreRadius_sq]
    dsimp only [coreEnergy]
    nlinarith only [sq_pos_of_neg (sub_neg.mpr hm)]
  have hspeed : exitTailSpeed (coreRadius (y 0) (y 2)) (y 1) (y 2) (y 3) ≠ 0 := by
    rwa [← exitClockRate_tail hm]
  have HF := contDiffAt_exitTailField n (v := y 2) (Y := toExitTailState y) hvR hrad.ne' hspeed
  have H : ContDiffAt ℝ n (fun p : ℝ × ExitTailState => exitTailField p.1 p.2)
      (Real.exp (-exitLogClock y), toExitTailState y) := by
    simpa only [exp_neg_exitLogClock hV] using HF
  have hmap : ContDiffAt ℝ n (fun p : ℝ × ExitTailState => (Real.exp (-p.1), p.2))
      (exitLogClock y, toExitTailState y) := by fun_prop
  exact H.comp (exitLogClock y, toExitTailState y) hmap

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.hasDerivAt_exitClockFlow_variation {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {t : ℝ} (ht : t ∈ I)
    (v : ExitTailState) :
    HasDerivAt (fun s => fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))
      (fderiv ℝ (exitTailField (Real.exp (-exitEntryClock (Y, t))))
        (exitClockFlow I (Y, exitEntryClock (Y, t)))
        (fderiv ℝ (exitClockFlow I) (Y, exitEntryClock (Y, t)) (v, 0)))
      (exitEntryClock (Y, t)) := by
  have HR := H Y hY t ht
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have HF : DifferentiableAt ℝ (fun p : ℝ × ExitTailState => exitTailField (Real.exp (-p.1)) p.2)
      (exitEntryClock (Y, t), exitClockFlow I (Y, exitEntryClock (Y, t))) := by
    rw [exitClockFlow_eq hI (H Y hY) ht]
    exact (contDiffAt_exitClockField HR.2.2.2.2.1 HR.2.2.2.2.2.1 HR.2.2.2.2.2.2.ne' 1).differentiableAt
      (by norm_num)
  exact hasDerivAt_parametric_first_variation (contDiffAt_exitClockFlow_two hIo hI ht HY)
    HF (exitClockFlow_local_partial_time hIo hI hUo hY H ht) v

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitEntryClock_interval_surjective {Y : ExitTailState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc 0 T, exitEntryRegular Y t) {s : ℝ}
    (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) :
    ∃ t ∈ Icc 0 T, exitEntryClock (Y, t) = s := by
  have HC : ContinuousOn (fun t => exitEntryClock (Y, t)) (Icc 0 T) :=
    HasDerivAt.continuousOn (fun t ht => hasDerivAt_exitEntryClock (H t ht))
  have H0 := exitEntryClock_initial (H 0 ⟨le_rfl, hT⟩).2.1
  exact intermediate_value_Icc hT HC (by rwa [H0])

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockFlow_on_interval {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) {s : ℝ} (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) :
    ContDiffAt ℝ 2 (exitClockFlow I) (Y, s) ∧
      HasDerivAt (fun r => exitClockFlow I (Y, r))
        (exitTailField (Real.exp (-s)) (exitClockFlow I (Y, s))) s ∧
      ∀ v : ExitTailState,
        HasDerivAt (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0))
          (fderiv ℝ (exitTailField (Real.exp (-s))) (exitClockFlow I (Y, s))
            (fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))) s := by
  obtain ⟨t, ht, he⟩ := exitEntryClock_interval_surjective hT (fun r hr => H Y hY r (hcover hr)) hs
  have HL := (exitClockFlow_local_ode hIo hI hUo hY H (hcover ht)).self_of_nhds
  have HV := hasDerivAt_exitClockFlow_variation hIo hI hUo hY H (hcover ht)
  rw [he] at HL HV
  exact ⟨HL.1, HL.2, HV⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreTailState_eq_exitClockFlow {I : Set ℝ} (hI : Convex ℝ I) {Y : ExitTailState} {h : ℝ}
    (H : ∀ r ∈ I, exitEntryRegular Y r) (hvalid : coreTailValid h Y)
    (ht : coreTailTime h Y ∈ I) :
    toExitTailState (coreTailState h Y) = exitClockFlow I (Y, -Real.log h) := by
  have HE := exitClockFlow_eq hI H ht
  have HC : exitEntryClock (Y, coreTailTime h Y) = -Real.log h := by
    change -Real.log (coreTailState h Y 2) = -Real.log h
    rw [coreTailState_active hvalid]
  rw [HC] at HE
  exact HE.symm

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.coreTailState_eventuallyEq_exitClockFlow {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {h : ℝ}
    (hvalid : coreTailValid h Y) (ht : coreTailTime h Y ∈ I) :
    (fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y]
      (fun Z => exitClockFlow I (Z, -Real.log h)) := by
  obtain ⟨hτ, _, hnear⟩ := coreTail_regular_of_valid (H Y hY _ ht).1 hvalid
  filter_upwards [hnear, hUo.mem_nhds hY, hτ.continuousAt.eventually (hIo.mem_nhds ht)] with Z hZ hZU hZI
  exact coreTailState_eq_exitClockFlow hI (H Z hZU) hZ hZI

end
end


/-- The radial cancellation and wall amplitudes hold for every higher endpoint of one finite tail. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ < 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η < 1 → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let F := fun Z => toExitTailState (coreTailState h Z)
      coreTailValid h Y ∧ ContDiffAt ℝ 2 F Y ∧ ‖fderiv ℝ F Y‖ ≤ C ∧
        |fderiv ℝ F Y (Pi.single 0 1) 0 - 1| ≤ C * (|u| + b ^ 2 * (1 + exitTailLength η α J) ^ 2) ∧
        ∀ i : Fin 2, |F Y i.succ| ≤ C * |Y i.succ| ∧
          |fderiv ℝ F Y (Pi.single 0 1) i.succ| ≤ C * |Y i.succ| / α := by
  obtain ⟨K, hK, εm, hεm, HM⟩ := exists_terminal_exitClock_multiplier_bounds hη₀ hJ
  obtain ⟨_, _, εr, hεr, HR⟩ := exists_exitTail_scale_bounds ⟨hη₀.1, hη₀.2.le⟩ hJ
  let L := Real.log (1 / η₀) + J * Real.exp (-1)
  have hL : 0 ≤ L := add_nonneg
    (Real.log_nonneg ((le_div_iff₀ hη₀.1).mpr (by linarith only [hη₀.2])))
    (mul_nonneg (Nat.cast_nonneg _) (Real.exp_pos _).le)
  have hK0 : 0 ≤ K := (by norm_num : (0 : ℝ) ≤ 1).trans hK
  let C := 1024 * K ^ 3 + K ^ 2 * (L + 1)
  have hradC : 1024 * K ^ 3 ≤ C := le_add_of_nonneg_right (by positivity)
  have hKC : K ≤ C := by
    have H1 : K ≤ K ^ 2 := by nlinarith only [hK]
    have H2 : K ^ 2 ≤ K ^ 3 := by nlinarith only [mul_nonneg (sq_nonneg K) (sub_nonneg.mpr hK)]
    nlinarith only [H1, H2, hradC, hK]
  have hwallC : K ^ 2 * L ≤ C := by
    dsimp only [C]
    nlinarith only [sq_nonneg K, (by positivity : 0 ≤ K ^ 3)]
  refine ⟨C, hK.trans hKC, min εm εr, lt_min hεm hεr, ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hsum Y h F
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have hsm := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εm εr) (pow_nonneg hα.1.le J))
  have hsr := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_right εm εr) (pow_nonneg hα.1.le J))
  obtain ⟨HV₀, I, hIo, hI, hcover, U, hUo, hYU, Htube, hinit, _, HF⟩ := HM α b u w hα hb hsm hsum
  have hh1 : h < 1 := by
    have H := mul_le_mul_of_nonneg_left (pow_le_one₀ hα.1.le hα.2 (n := J)) hη.le
    exact H.trans_lt (by simpa only [mul_one] using hηhi)
  obtain ⟨HV, htime⟩ := coreTailValid_of_height_le HV₀
    (mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)) hh1
  let S := exitTailLength η α J
  let S₀ := exitTailLength η₀ α J
  have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη, hηhi.le⟩ hα J
  have hS₀ : 0 ≤ S₀ := exitTailLength_nonneg ⟨hη₀.1, hη₀.2.le⟩ hα J
  have hSS₀ : S ≤ S₀ := by
    have H := mul_le_mul_of_nonneg_right hηlo (pow_nonneg hα.1.le J)
    rw [← exp_neg_exitTailLength hη₀.1 hα.1 J, ← exp_neg_exitTailLength hη hα.1 J] at H
    exact neg_le_neg_iff.mp (Real.exp_le_exp.mp H)
  have hs : S ∈ Icc 0 S₀ := ⟨hS, hSS₀⟩
  have hsub : Icc 0 S ⊆ Icc 0 S₀ := fun _ ht => ⟨ht.1, ht.2.trans hSS₀⟩
  have hT : 0 ≤ coreTailTime (η₀ * α ^ J) Y := HV₀.1.1.1.le
  have hclock : exitEntryClock (Y, coreTailTime (η₀ * α ^ J) Y) = S₀ := by
    change -Real.log (coreTailState (η₀ * α ^ J) Y 2) = S₀
    rw [coreTailState_active HV₀, ← exp_neg_exitTailLength hη₀.1 hα.1 J, Real.log_exp, neg_neg]
  have heh : -Real.log h = S := by
    change -Real.log (η * α ^ J) = S
    rw [← exp_neg_exitTailLength hη hα.1 J, Real.log_exp, neg_neg]
  have hend := coreTailState_eventuallyEq_exitClockFlow hIo hI hUo hYU Htube HV
    (hcover ⟨HV.1.1.1.le, htime⟩)
  rw [heh] at hend
  let β : ℝ → ExitTailState := fun s => exitClockFlow I (Y, s)
  have hβ0 : β 0 = Y := hinit
  have hR : β 0 0 = 2 + 2 * α := by rw [hβ0]; rfl
  have hwall : |β 0 1| + |β 0 2| ≤ b := by rw [hβ0]; exact hsum
  have hβ (s : ℝ) (hs : s ∈ Icc 0 S₀) : HasDerivAt β (exitTailField (Real.exp (-s)) (β s)) s :=
    (exitClockFlow_on_interval hIo hI hUo hYU Htube hT hcover (hclock ▸ hs)).2.1
  have HP := HR α b S₀ β hα hb hsr ⟨hS₀, le_rfl⟩ hR hwall hβ
  have hreg (s : ℝ) (hs : s ∈ Icc 0 S₀) :=
    And.intro (HP s hs).1.1 (And.intro (HP s hs).1.2.1 (HP s hs).1.2.2.1)
  have hmult (s : ℝ) (hs : s ∈ Icc 0 S₀) (i : Fin 2) :
      Real.exp (exitClockLogMultiplier I i Y s) ≤ K ∧
        ‖fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y‖ ≤ K * s := by
    refine ⟨((HF s hs).2.2.1 i).2.2.2.1, ?_⟩
    have Hsum : ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 0 Z s) Y‖ +
      ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 1 Z s) Y‖ ≤ K * s := (HF s hs).2.2.2
    fin_cases i
    · exact (le_add_of_nonneg_right (norm_nonneg _)).trans Hsum
    · exact (le_add_of_nonneg_left (norm_nonneg _)).trans Hsum
  have Hslice : ContDiffAt ℝ 2 (fun Z => exitClockFlow I (Z, S)) Y :=
    ContDiffAt.comp (g := exitClockFlow I) (f := fun Z : ExitTailState => (Z, S)) Y
      (HF S hs).1 (contDiffAt_id.prodMk (contDiffAt_const (c := S)))
  have Hder : fderiv ℝ F Y = fderiv ℝ (fun Z => exitClockFlow I (Z, S)) Y := hend.fderiv_eq
  have Hpoint : F Y = exitClockFlow I (Y, S) := hend.self_of_nhds
  refine ⟨HV, Hslice.congr_of_eventuallyEq hend, ?_, ?_, ?_⟩
  · rw [Hder]
    exact (HF S hs).2.1.trans hKC
  · rw [Hder]
    have H := exitClock_radial_column_bound hIo hI hUo hYU Htube hT hcover (hclock ▸ hs) hK
      (show |Y 1| + |Y 2| ≤ b from hsum) (fun r hr => hreg r (hsub hr))
      (fun r hr => (HF r (hsub hr)).2.1) (fun r hr => hmult r (hsub hr))
      (Pi.single 0 1) (by simp)
    simp only [Pi.single_eq_same, Pi.single_eq_of_ne (by decide : (2 : Fin 3) ≠ 0),
      abs_zero, mul_zero, zero_mul, add_zero, Pi.norm_single, norm_one, mul_one] at H
    change _ ≤ 512 * K ^ 3 * (2 * |u| + b ^ 2 * S * (1 + S)) at H
    refine H.trans ((show 512 * K ^ 3 * (2 * |u| + b ^ 2 * S * (1 + S)) ≤
      1024 * K ^ 3 * (|u| + b ^ 2 * (1 + S) ^ 2) from ?_).trans
      (mul_le_mul_of_nonneg_right hradC (by positivity)))
    have HE : S * (1 + S) ≤ (1 + S) ^ 2 := by nlinarith only [hS]
    nlinarith only [mul_le_mul_of_nonneg_left HE (by positivity : 0 ≤ K ^ 3 * b ^ 2),
      (by positivity : 0 ≤ K ^ 3 * b ^ 2 * (1 + S) ^ 2)]
  · intro i
    have Hval := ((HF S hs).2.2.1 i).1
    have hamp : |F Y i.succ| ≤ K * |Y i.succ| := by
      rw [Hpoint, Hval, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact (mul_le_mul_of_nonneg_left (hmult S hs i).1 (abs_nonneg _)).trans_eq (by ring)
    refine ⟨hamp.trans (mul_le_mul_of_nonneg_right hKC (abs_nonneg _)), ?_⟩
    rw [Hder, ((HF S hs).2.2.1 i).2.2.2.2]
    have hz : (Pi.single 0 1 : ExitTailState) i.succ = 0 := by fin_cases i <;> simp
    rw [hz, mul_zero, zero_add, abs_mul, ← Hpoint]
    have Hlog := (fderiv ℝ (fun Z => exitClockLogMultiplier I i Z S) Y).le_opNorm (Pi.single 0 1)
    simp only [Pi.norm_single, norm_one, mul_one, Real.norm_eq_abs] at Hlog
    have Hlength : S ≤ L / α := hSS₀.trans ((le_div_iff₀ hα.1).mpr (by
      simpa only [mul_comm] using (exitTailLength_weighted_bounds ⟨hη₀.1, hη₀.2.le⟩ hα J).1))
    calc
      _ ≤ (K * |Y i.succ|) * (K * (L / α)) :=
        mul_le_mul hamp (Hlog.trans ((hmult S hs i).2.trans (mul_le_mul_of_nonneg_left Hlength hK0)))
          (abs_nonneg _) (by positivity)
      _ = (K ^ 2 * L) * |Y i.succ| / α := by ring
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hwallC (abs_nonneg _)) hα.1.le
