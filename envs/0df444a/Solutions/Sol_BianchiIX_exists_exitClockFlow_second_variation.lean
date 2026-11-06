-- Prove2me | solution 1 for BianchiIX.exists_exitClockFlow_second_variation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:01:22.530272+00:00
-- url     : https://prove2.me/submissions/7e9d622e-5b69-4ce4-a6d8-7d1295fbe6b9

import Definitions.Def_BianchiIX_Dynamics_Normalized
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConeData
import Definitions.Def_BianchiIX_Algebra_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_Dynamics_MaximalFlow
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Definitions.Def_BianchiIX_Dynamics_CoreAngle
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_scalar_event_branch_two
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toExitTailState
import Theorems.Thm_BianchiIX_hasFDerivAt_compact_vector_integral
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

private theorem BianchiIX.fderiv_parameterSlice_apply {Φ : E × ℝ → F} {x : E} {t : ℝ}
    (H : DifferentiableAt ℝ Φ (x, t)) (v : E) :
    fderiv ℝ (fun y => Φ (y, t)) x v = fderiv ℝ Φ (x, t) (v, 0) := by
  have HD := H.hasFDerivAt.comp x (hasFDerivAt_prodMk_left (𝕜 := ℝ) x t)
  change HasFDerivAt (fun y => Φ (y, t)) _ x at HD
  rw [HD.fderiv]
  rfl

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.contDiffAt_parameterVariation {Φ : E × ℝ → F} {x : E} {t : ℝ}
    (H : ContDiffAt ℝ 2 Φ (x, t)) (w : E) :
    ContDiffAt ℝ 1 (fun p => fderiv ℝ Φ p (w, 0)) (x, t) :=
  (H.fderiv_right (m := 1) (by norm_num)).clm_apply contDiffAt_const

end
end

section
noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem BianchiIX.fderiv_parameterVariation_apply {Φ : E × ℝ → F} {x : E} {t : ℝ}
    (H : ContDiffAt ℝ 2 Φ (x, t)) (v w : E) :
    fderiv ℝ (fun y => fderiv ℝ Φ (y, t) (w, 0)) x v =
      fderiv ℝ (fderiv ℝ (fun y => Φ (y, t))) x v w := by
  have heq : (fun y => fderiv ℝ Φ (y, t) (w, 0)) =ᶠ[𝓝 x]
      (fun y => fderiv ℝ (fun z => Φ (z, t)) y w) := by
    have hnear := (continuousAt_id.prodMk continuousAt_const).eventually (H.eventually (by norm_num))
    filter_upwards [hnear] with y hy
    exact (fderiv_parameterSlice_apply (hy.differentiableAt (by norm_num)) w).symm
  have hslice : ContDiffAt ℝ 2 (fun y => Φ (y, t)) x :=
    H.comp x (contDiffAt_id.prodMk contDiffAt_const)
  have HD := ((hslice.fderiv_right (m := 1) (by norm_num)).differentiableAt
    (by norm_num)).hasFDerivAt.clm_apply (hasFDerivAt_const w x)
  rw [heq.fderiv_eq, HD.fderiv]
  simp

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

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

private theorem BianchiIX.hasFDerivAt_of_parametric_ode
    {J G : E × ℝ → V} {x : E} {a b : ℝ} {v : V}
    (hab : a ≤ b) (hG : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 G (x, t))
    (hJ : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => J (y, r)) (G (y, t)) t)
    (hinit : ∀ᶠ y in 𝓝 x, J (y, a) = v) :
    HasFDerivAt (fun y => J (y, b))
      (∫ t in a..b, (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)) x := by
  have hnear : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b, ContDiffAt ℝ 1 G (y, t) := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    exact (hG t ht).eventually (by norm_num)
  have heq : (fun y => J (y, b)) =ᶠ[𝓝 x] (fun y => v + ∫ t in a..b, G (y, t)) := by
    filter_upwards [hJ, hinit, hnear] with y hy hi hc
    have hcont : ContinuousOn (fun t => G (y, t)) (Icc a b) := fun t ht =>
      ((hc t ht).continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
    have H := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (fun t ht => hy t (uIcc_of_le hab ▸ ht)) (hcont.intervalIntegrable_of_Icc hab)
    rw [hi] at H
    rw [H, add_sub_cancel]
  have H := (hasFDerivAt_const v x).add (hasFDerivAt_compact_vector_integral hab hG)
  simpa only [zero_add] using H.congr_of_eventuallyEq heq

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

private theorem BianchiIX.hasDerivAt_integral_partial_fderiv {G : E × ℝ → V} {x : E} {a b : ℝ}
    (hab : a ≤ b) (hG : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 G (x, t)) :
    HasDerivAt
      (fun s => ∫ t in a..s, (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ))
      ((fderiv ℝ G (x, b)).comp (ContinuousLinearMap.inl ℝ E ℝ)) b := by
  let S : Set ℝ := {t | ContDiffAt ℝ 1 G (x, t)}
  let D := fun t => (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  have hS : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro t ht
    change ContDiffAt ℝ 1 G (x, t) at ht
    exact (continuousAt_const.prodMk (continuousAt_id (x := t))).eventually
      (ht.eventually (by norm_num))
  have hD : ContinuousOn D S := by
    intro t ht
    change ContDiffAt ℝ 1 G (x, t) at ht
    exact (((ht.continuousAt_fderiv (by norm_num)).clm_comp continuousAt_const).comp
      (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hb : b ∈ S := hG b ⟨hab, le_rfl⟩
  exact intervalIntegral.integral_hasDerivAt_right
    ((hD.mono (fun t ht => hG t ht)).intervalIntegrable_of_Icc hab)
    (hD.stronglyMeasurableAtFilter hS b hb) (hD.continuousAt (hS.mem_nhds hb))

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [CompleteSpace V]

private theorem BianchiIX.exists_parametric_variation_integral
    {J G : E × ℝ → V} {x : E} {a b : ℝ} {w : V}
    (hG : ∀ t ∈ Icc a b, ContDiffAt ℝ 1 G (x, t))
    (hJ : ∀ᶠ y in 𝓝 x, ∀ t ∈ Icc a b,
      HasDerivAt (fun r => J (y, r)) (G (y, t)) t)
    (hinit : ∀ᶠ y in 𝓝 x, J (y, a) = w) (v : E) :
    ∃ Q : ℝ → V, Q a = 0 ∧ ∀ t ∈ Icc a b,
      Q t = fderiv ℝ (fun y => J (y, t)) x v ∧
      HasDerivAt Q (fderiv ℝ G (x, t) (v, 0)) t := by
  let D := fun t => (fderiv ℝ G (x, t)).comp (ContinuousLinearMap.inl ℝ E ℝ)
  refine ⟨fun t => (∫ r in a..t, D r) v, by simp, ?_⟩
  intro t ht
  have hsub : Icc a t ⊆ Icc a b := fun _ hr => ⟨hr.1, hr.2.trans ht.2⟩
  have HG := fun r hr => hG r (hsub hr)
  have HJ : ∀ᶠ y in 𝓝 x, ∀ r ∈ Icc a t, HasDerivAt (fun s => J (y, s)) (G (y, r)) r :=
    hJ.mono fun _ hy r hr => hy r (hsub hr)
  have HD := hasFDerivAt_of_parametric_ode ht.1 HG HJ hinit
  refine ⟨by rw [HD.fderiv], ?_⟩
  have HI := (hasDerivAt_integral_partial_fderiv ht.1 HG).clm_apply (hasDerivAt_const t v)
  simpa [D] using HI

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

private theorem BianchiIX.toExitTailState_fromExitTailState {v : ℝ} {Y : ExitTailState}
    (hR : 0 < Y 0) (hv : v ^ 2 ≤ (Y 0) ^ 2) :
    toExitTailState (fromExitTailState v Y) = Y := by
  have hs := exitTailGap_sq hv
  have he : coreEnergy (1 - exitTailGap (Y 0) v) v = (Y 0) ^ 2 := by
    dsimp only [coreEnergy]
    nlinarith only [hs]
  ext i
  fin_cases i
  · change Real.sqrt (coreEnergy (1 - exitTailGap (Y 0) v) v) = Y 0
    rw [he, Real.sqrt_sq hR.le]
  · rfl
  · rfl

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
open Set Filter
open scoped Topology

private theorem BianchiIX.toExitTailState_coreTailEntry {Y : ExitTailState} (hR : 1 < Y 0) :
    toExitTailState (coreTailEntry Y) = Y := by
  have HE := toExitTailState_fromExitTailState (Y := Y) (v := 1)
    (by linarith only [hR]) (by nlinarith only [hR])
  simpa only [coreTailEntry, fromExitTailState, exitTailGap, one_pow] using HE

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

private theorem BianchiIX.exitClockFlow_initial {I : Set ℝ} (hI : Convex ℝ I) {Y : ExitTailState}
    (H : ∀ r ∈ I, exitEntryRegular Y r) (h0 : (0 : ℝ) ∈ I) : exitClockFlow I (Y, 0) = Y := by
  have HR := H 0 h0
  have HE := exitClockFlow_eq hI H h0
  rw [exitEntryClock_initial HR.2.1] at HE
  exact HE.trans (by
    rw [exitEntryFlow, projectiveOriginalFlow_initial HR.2.1]
    exact toExitTailState_coreTailEntry HR.1)

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

private theorem BianchiIX.exitClockFlow_variation_initial {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) (h0 : (0 : ℝ) ∈ I) (v : ExitTailState) :
    fderiv ℝ (exitClockFlow I) (Y, 0) (v, 0) = v := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have HC := contDiffAt_exitClockFlow_two hIo hI h0 HY
  rw [exitEntryClock_initial (H Y hY 0 h0).2.1] at HC
  have HE : (fun Z => exitClockFlow I (Z, 0)) =ᶠ[𝓝 Y] id := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact exitClockFlow_initial hI (H Z hZ) h0
  have hslice : HasFDerivAt (fun Z : ExitTailState => (Z, (0 : ℝ)))
      ((ContinuousLinearMap.id ℝ ExitTailState).prod 0) Y :=
    (hasFDerivAt_id Y).prodMk (hasFDerivAt_const (0 : ℝ) Y)
  have HD := (HC.differentiableAt (by norm_num)).hasFDerivAt.comp Y hslice
  have HI := (HD.congr_of_eventuallyEq HE.symm).unique (hasFDerivAt_id Y)
  exact congrArg (fun L : ExitTailState →L[ℝ] ExitTailState => L v) HI

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

private theorem BianchiIX.contDiffAt_exitClock_stateDerivative {y : ProjectiveState} (hV : 0 < y 2)
    (hm : y 0 < 1) (hd : exitClockRate y ≠ 0) :
    ContDiffAt ℝ 1 (fun p : ℝ × ExitTailState => fderiv ℝ (exitTailField (Real.exp (-p.1))) p.2)
      (exitLogClock y, toExitTailState y) := by
  have hmap : ContDiffAt ℝ 2
      (fun p : (ℝ × ExitTailState) × ExitTailState => (p.1.1, p.2))
      ((exitLogClock y, toExitTailState y), toExitTailState y) := by fun_prop
  have HF := (contDiffAt_exitClockField hV hm hd 2).comp
    ((exitLogClock y, toExitTailState y), toExitTailState y) hmap
  exact HF.fderiv (f := fun p : ℝ × ExitTailState => exitTailField (Real.exp (-p.1)))
    contDiffAt_snd (by norm_num)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_exitClockVariationRate_one {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hΦ : ContDiffAt ℝ 2 (exitClockFlow I) (Y, s))
    (hA : ContDiffAt ℝ 1 (fun p : ℝ × ExitTailState => fderiv ℝ (exitTailField (Real.exp (-p.1))) p.2)
      (s, exitClockFlow I (Y, s))) (w : ExitTailState) :
    ContDiffAt ℝ 1 (exitClockVariationRate I w) (Y, s) := by
  have HD := hA.comp (Y, s) (contDiffAt_snd.prodMk (hΦ.of_le (by norm_num : (1 : WithTop ℕ∞) ≤ 2)))
  exact HD.clm_apply (contDiffAt_parameterVariation hΦ w)

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockVariationRate_fderiv_initial {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hΦ : ContDiffAt ℝ 2 (exitClockFlow I) (Y, s))
    (hA : ContDiffAt ℝ 1 (fun p : ℝ × ExitTailState => fderiv ℝ (exitTailField (Real.exp (-p.1))) p.2)
      (s, exitClockFlow I (Y, s))) (v w : ExitTailState) :
    fderiv ℝ (exitClockVariationRate I w) (Y, s) (v, 0) =
      fderiv ℝ (exitTailField (Real.exp (-s))) (exitClockFlow I (Y, s))
        (fderiv ℝ (fun Z => fderiv ℝ (exitClockFlow I) (Z, s) (w, 0)) Y v) +
      fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (exitClockFlow I (Y, s))
        (fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))
        (fderiv ℝ (exitClockFlow I) (Y, s) (w, 0)) := by
  have hFs := (hΦ.differentiableAt (by norm_num)).hasFDerivAt.comp Y
    (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y s)
  have hJs : DifferentiableAt ℝ (fun Z => fderiv ℝ (exitClockFlow I) (Z, s) (w, 0)) Y := by
    have HJ := ((contDiffAt_parameterVariation hΦ w).differentiableAt (by norm_num)).comp Y
      ((hasFDerivAt_prodMk_left (𝕜 := ℝ) Y s).differentiableAt)
    exact HJ
  have hAs : DifferentiableAt ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (exitClockFlow I (Y, s)) :=
    (hA.differentiableAt (by norm_num)).comp _
      ((hasFDerivAt_const s _).prodMk (hasFDerivAt_id _)).differentiableAt
  have Hprod := (hAs.hasFDerivAt.comp Y hFs).clm_apply hJs.hasFDerivAt
  have Hpart := ((contDiffAt_exitClockVariationRate_one hΦ hA w).differentiableAt
    (by norm_num)).hasFDerivAt.comp Y (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y s)
  have HE := congrArg (fun L : ExitTailState →L[ℝ] ExitTailState => L v) (Hpart.unique Hprod)
  simpa only [Function.comp_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.inl_apply, add_apply,
    ContinuousLinearMap.flip_apply] using HE

end
end

private theorem BianchiIX.exitClockFlow_graph_regular {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {Y : ExitTailState} {t : ℝ} (ht : t ∈ I)
    (H : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r) :
    ContDiffAt ℝ 2 (exitClockFlow I) (Y, exitEntryClock (Y, t)) ∧
      ContDiffAt ℝ 1 (fun p : ℝ × ExitTailState => fderiv ℝ (exitTailField (Real.exp (-p.1))) p.2)
        (exitEntryClock (Y, t), exitClockFlow I (Y, exitEntryClock (Y, t))) := by
  have HR := H.self_of_nhds t ht
  refine ⟨contDiffAt_exitClockFlow_two hIo hI ht H, ?_⟩
  rw [exitClockFlow_eq hI H.self_of_nhds ht]
  exact contDiffAt_exitClock_stateDerivative HR.2.2.2.2.1 HR.2.2.2.2.2.1 HR.2.2.2.2.2.2.ne'

private theorem BianchiIX.exitClockFlow_local_variation {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {t : ℝ} (ht : t ∈ I) (w : ExitTailState) :
    ∀ᶠ p in 𝓝 (Y, exitEntryClock (Y, t)),
      ContDiffAt ℝ 1 (exitClockVariationRate I w) p ∧
      HasDerivAt (fun s => fderiv ℝ (exitClockFlow I) (p.1, s) (w, 0))
        (exitClockVariationRate I w p) p.2 := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have Hp := (show ContinuousAt (fun p : ExitTailState × ℝ => p.1)
    (Y, exitEntryClock (Y, t)) from continuousAt_fst).eventually (hUo.mem_nhds hY)
  filter_upwards [(exitClockTime_regular hIo hI ht HY).2, Hp] with p hp hpu
  have HZ : ∀ᶠ Z in 𝓝 p.1, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hpu] with Z hZ
    exact H Z hZ
  have HR := exitClockFlow_graph_regular hIo hI hp.1 HZ
  have HD := hasDerivAt_exitClockFlow_variation hIo hI hUo hpu H hp.1 w
  rw [hp.2] at HR HD
  exact ⟨contDiffAt_exitClockVariationRate_one HR.1 HR.2 w, HD⟩


/-- The ordinary Hessian of the actual clock map is represented by the forced variational system. -/
theorem solution {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (v w : ExitTailState) :
    ∃ Q : ℝ → ExitTailState, Q 0 = 0 ∧ ∀ s ∈ Icc 0 (exitEntryClock (Y, T)),
      Q s = fderiv ℝ (fderiv ℝ (fun Z => exitClockFlow I (Z, s))) Y v w ∧
      HasDerivAt Q
        (fderiv ℝ (exitTailField (Real.exp (-s))) (exitClockFlow I (Y, s)) (Q s) +
          fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (exitClockFlow I (Y, s))
            (fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))
            (fderiv ℝ (exitClockFlow I) (Y, s) (w, 0))) s := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  have Hpre {s : ℝ} (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) :
      ∃ t ∈ Icc 0 T, exitEntryClock (Y, t) = s :=
    exitEntryClock_interval_surjective hT (fun t ht => H Y hY t (hcover ht)) hs
  have HG (s : ℝ) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) :
      ContDiffAt ℝ 1 (exitClockVariationRate I w) (Y, s) := by
    obtain ⟨t, ht, he⟩ := Hpre hs
    simpa only [he] using (exitClockFlow_local_variation hIo hI hUo hY H (hcover ht) w).self_of_nhds.1
  have HJ : ∀ᶠ Z in 𝓝 Y, ∀ s ∈ Icc 0 (exitEntryClock (Y, T)),
      HasDerivAt (fun r => fderiv ℝ (exitClockFlow I) (Z, r) (w, 0))
        (exitClockVariationRate I w (Z, s)) s := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro s hs
    obtain ⟨t, ht, he⟩ := Hpre hs
    have HL := (exitClockFlow_local_variation hIo hI hUo hY H (hcover ht) w).mono fun _ h => h.2
    simpa only [he] using HL
  have hi : ∀ᶠ Z in 𝓝 Y, fderiv ℝ (exitClockFlow I) (Z, 0) (w, 0) = w := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact exitClockFlow_variation_initial hIo hI hUo hZ H (hcover ⟨le_rfl, hT⟩) w
  obtain ⟨Q, hQ0, HQ⟩ := exists_parametric_variation_integral
    (J := fun p : ExitTailState × ℝ => fderiv ℝ (exitClockFlow I) p (w, 0))
    (G := exitClockVariationRate I w) HG HJ hi v
  refine ⟨Q, hQ0, ?_⟩
  intro s hs
  obtain ⟨t, ht, he⟩ := Hpre hs
  have HR := exitClockFlow_graph_regular hIo hI (hcover ht) HY
  rw [he] at HR
  refine ⟨(HQ s hs).1.trans (fderiv_parameterVariation_apply HR.1 v w), ?_⟩
  have HD := (HQ s hs).2
  rwa [exitClockVariationRate_fderiv_initial HR.1 HR.2 v w, ← (HQ s hs).1] at HD
