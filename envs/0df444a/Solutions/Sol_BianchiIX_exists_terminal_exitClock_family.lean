-- Prove2me | solution 1 for BianchiIX.exists_terminal_exitClock_family
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:02:07.935525+00:00
-- url     : https://prove2.me/submissions/8db9b865-8c9f-43c7-a5b4-67655ec8ac3c

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
import Definitions.Def_BianchiIX_Dynamics_FlowRegularity
import Definitions.Def_BianchiIX_Dynamics_Events
import Definitions.Def_BianchiIX_Dynamics_ProjectiveFlowVariation
import Definitions.Def_BianchiIX_Dynamics_CoreTail
import Theorems.Thm_BianchiIX_contDiffAt_fromProjectiveState
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_exists_Ioo_covering_Icc
import Theorems.Thm_BianchiIX_exists_scalar_event_branch_two
import Theorems.Thm_BianchiIX_exists_terminal_coreTail_valid
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toExitTailState
import Theorems.Thm_BianchiIX_normalizedMaxCurve_regular
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
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_Ioo_covering_of_eventually {s t : ℝ} {P : ℝ → Prop} (hst : s ≤ t)
    (hP : ∀ u ∈ Icc s t, ∀ᶠ v in 𝓝 u, P v) :
    ∃ l r : ℝ, l < s ∧ t < r ∧ ∀ u ∈ Ioo l r, P u := by
  obtain ⟨l, r, hls, htr, hsub⟩ := exists_Ioo_covering_Icc hst isOpen_interior
    (fun u hu => mem_interior_iff_mem_nhds.mpr (hP u hu))
  exact ⟨l, r, hls, htr, fun u hu => interior_subset (hsub hu)⟩

end
end

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

private theorem BianchiIX.exitTailGap_sq {R v : ℝ} (h : v ^ 2 ≤ R ^ 2) :
    exitTailGap R v ^ 2 = R ^ 2 - v ^ 2 := Real.sq_sqrt (sub_nonneg.mpr h)

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailGap_compact {R v : ℝ} (hR : 7 / 4 ≤ R) (hv : 0 ≤ v ∧ v ≤ 1) :
    1 ≤ exitTailGap R v ∧ exitTailGap R v ≤ R := by
  have hR0 : 0 ≤ R := by linarith only [hR]
  have hv2 : v ^ 2 ≤ 1 := by nlinarith only [hv.1, hv.2]
  refine ⟨?_, ?_⟩
  · exact (Real.le_sqrt (by norm_num) (by nlinarith only [hR, hv2])).mpr
      (by nlinarith only [hR, hv2])
  · exact (Real.sqrt_le_left hR0).mpr (by nlinarith only [sq_nonneg v])

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTail_coupling_bound {u v w : ℝ} (hv : 0 ≤ v) :
    |coupling u v w| ≤ |u| * v + (|u| + |w|) ^ 2 := by
  have H : |v + w - u| ≤ v + |w| + |u| := by
    exact (abs_sub _ _).trans (add_le_add ((abs_add_le v w).trans_eq (by rw [abs_of_nonneg hv])) le_rfl)
  rw [coupling, abs_mul]
  have H' := mul_le_mul_of_nonneg_left H (abs_nonneg u)
  nlinarith only [H', mul_nonneg (abs_nonneg u) (abs_nonneg w), sq_nonneg |w|]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailSpeed_compact {R u v w : ℝ} (hR : 7 / 4 ≤ R)
    (hu : |u| ≤ 1 / 100) (hv : 0 ≤ v ∧ v ≤ 1) (hw : |w| ≤ 1 / 100) :
    1 / 2 ≤ exitTailSpeed R u v w := by
  have ht := (exitTailGap_compact hR hv).1
  have hc := exitTail_coupling_bound (u := u) (w := w) hv.1
  have huv : |u| * v ≤ 1 / 100 := by
    nlinarith only [mul_le_mul_of_nonneg_left hv.2 (abs_nonneg u), hu]
  have hb : (|u| + |w|) ^ 2 ≤ (1 / 50 : ℝ) ^ 2 := by
    nlinarith only [hu, hw, abs_nonneg u, abs_nonneg w]
  have H := neg_abs_le (coupling u v w)
  dsimp only [exitTailSpeed]
  linarith only [ht, hc, huv, hb, H]

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
open scoped Topology

private theorem BianchiIX.isOpen_normalizedFlowDomain (t₀ : ℝ) : IsOpen (normalizedFlowDomain t₀) := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  exact mem_interior_iff_mem_nhds.mp (normalizedMaxCurve_regular hz).1

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

private theorem BianchiIX.contDiff_exitClockRate (n : WithTop ℕ∞) : ContDiff ℝ n exitClockRate := by
  unfold exitClockRate coupling
  fun_prop

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

private theorem BianchiIX.exitClockRate_compact {y : ProjectiveState} (hm : y 0 < 1)
    (hR : 7 / 4 ≤ coreRadius (y 0) (y 2))
    (hu : |y 1| ≤ 1 / 100) (hv : 0 ≤ y 2 ∧ y 2 ≤ 1) (hw : |y 3| ≤ 1 / 100) :
    1 / 2 ≤ exitClockRate y := by
  rw [exitClockRate_tail hm]
  exact exitTailSpeed_compact hR hu hv hw

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
open Set

private theorem BianchiIX.exitPhysicalRegion_clock {h : ℝ} {y : ProjectiveState} (hh : 0 < h)
    (hy : exitPhysicalRegion h y) : 1 / 2 ≤ exitClockRate y :=
  exitClockRate_compact (lt_of_le_of_lt hy.1 (by norm_num)) hy.2.1.1 hy.2.2.1
    ⟨(hh.trans_le hy.2.2.2.1.1).le, hy.2.2.2.1.2⟩ hy.2.2.2.2

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
open Set

private theorem BianchiIX.coreTailValid_denom_pos {η : ℝ} {Y : CoreAngleState} (hvalid : coreTailValid η Y) :
    0 < projectiveStateDenom (coreTailEntry Y) := by
  have hzero := (hvalid.2.1 0 ⟨le_rfl, hvalid.1.1.1.le⟩).2
  rw [normalizedMaxCurve_initial] at hzero
  change 0 < 1 + (6 / projectiveStateDenom (coreTailEntry Y) - 1) at hzero
  by_contra! hn
  have H := div_nonpos_of_nonneg_of_nonpos (by norm_num : (0 : ℝ) ≤ 6) hn
  linarith only [hzero, H]

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

private theorem BianchiIX.isOpen_exitEntryRegular : IsOpen {p : ExitTailState × ℝ | exitEntryRegular p.1 p.2} := by
  apply isOpen_iff_mem_nhds.mpr
  intro p hp
  have he := contDiffAt_coreTailEntry 2 hp.1
  have hentry : ContDiffAt ℝ 2 (fun q : ExitTailState × ℝ => coreTailEntry q.1) p :=
    he.comp p contDiffAt_fst
  have hparam : ContDiffAt ℝ 2 (fun q : ExitTailState × ℝ =>
      (fromProjectiveState (coreTailEntry q.1), q.2)) p := by
    have HF := (contDiffAt_fromProjectiveState 2 hp.2.1.ne').comp p hentry
    exact HF.prodMk contDiffAt_snd
  have hN : ContinuousAt (fun q : ExitTailState × ℝ =>
      normalizedMaxCurve (fromProjectiveState (coreTailEntry q.1)) 0 q.2) p := by
    exact ((contDiffAt_normalizedMaxCurve_two hp.2.2.1).comp p hparam).continuousAt
  have hflow := (contDiffAt_exitEntryFlow_two hp).continuousAt
  have hR : ContinuousAt (fun q : ExitTailState × ℝ => q.1 0) p := by fun_prop
  have hden := continuous_projectiveStateDenom.continuousAt.comp hentry.continuousAt
  have hdom := hparam.continuousAt.eventually ((isOpen_normalizedFlowDomain 0).mem_nhds hp.2.2.1)
  have hA : ContinuousAt (fun q : ExitTailState × ℝ =>
      1 + normalizedMaxCurve (fromProjectiveState (coreTailEntry q.1)) 0 q.2 0) p :=
    continuousAt_const.add (continuousAt_pi.mp hN 0)
  have hrate := (contDiff_exitClockRate 1).continuous.continuousAt.comp hflow
  filter_upwards [hR.eventually (isOpen_Ioi.mem_nhds hp.1),
    hden.eventually (isOpen_Ioi.mem_nhds hp.2.1), hdom,
    hA.eventually (isOpen_Ioi.mem_nhds hp.2.2.2.1),
    (continuousAt_pi.mp hflow 2).eventually (isOpen_Ioi.mem_nhds hp.2.2.2.2.1),
    (continuousAt_pi.mp hflow 0).eventually (isOpen_Iio.mem_nhds hp.2.2.2.2.2.1),
    hrate.eventually (isOpen_Ioi.mem_nhds hp.2.2.2.2.2.2)] with q hqR hqD hqd hqA hqV hqM hqrate
  exact ⟨hqR, hqD, hqd, hqA, hqV, hqM, hqrate⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exists_exitEntry_regular_tube {Y : ExitTailState} {T : ℝ} (hT : 0 ≤ T)
    (H : ∀ t ∈ Icc 0 T, exitEntryRegular Y t) :
    ∃ U : Set ExitTailState, IsOpen U ∧ Y ∈ U ∧ ∃ l r : ℝ,
      l < 0 ∧ T < r ∧ ∀ Z ∈ U, ∀ t ∈ Ioo l r, exitEntryRegular Z t := by
  have htime (t : ℝ) (ht : t ∈ Icc 0 T) : ∀ᶠ s in 𝓝 t, exitEntryRegular Y s :=
    (continuousAt_const.prodMk continuousAt_id).eventually (isOpen_exitEntryRegular.mem_nhds (H t ht))
  obtain ⟨l, r, hl, hr, hinterval⟩ := exists_Ioo_covering_of_eventually hT htime
  let a := l / 2
  let b := (T + r) / 2
  have ha : l < a ∧ a < 0 := by dsimp only [a]; constructor <;> linarith only [hl]
  have hb : T < b ∧ b < r := by dsimp only [b]; constructor <;> linarith only [hr]
  have hcompact : ∀ᶠ Z in 𝓝 Y, ∀ t ∈ Icc a b, exitEntryRegular Z t := by
    apply isCompact_Icc.eventually_forall_of_forall_eventually
    intro t ht
    have hreg := hinterval t ⟨ha.1.trans_le ht.1, ht.2.trans_lt hb.2⟩
    exact isOpen_exitEntryRegular.mem_nhds hreg
  obtain ⟨U, hU, hUopen, hYU⟩ := mem_nhds_iff.mp hcompact
  exact ⟨U, hUopen, hYU, a, b, ha.2, hb.1, fun Z hZ t ht => hU hZ t (Ioo_subset_Icc_self ht)⟩

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


/-- The terminal Einstein flight has one joint C2 clock family, including its initial endpoint. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧
        Icc 0 (coreTailTime h Y) ⊆ I ∧ ∃ U : Set ExitTailState, IsOpen U ∧ Y ∈ U ∧
        (∀ Z ∈ U, ∀ t ∈ I, exitEntryRegular Z t) ∧
        exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S, ContDiffAt ℝ 2 (exitClockFlow I) (Y, s) ∧
          HasDerivAt (fun r => exitClockFlow I (Y, r))
            (exitTailField (Real.exp (-s)) (exitClockFlow I (Y, s))) s ∧
          ∀ v : ExitTailState,
            HasDerivAt (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0))
              (fderiv ℝ (exitTailField (Real.exp (-s))) (exitClockFlow I (Y, s))
                (fderiv ℝ (exitClockFlow I) (Y, s) (v, 0))) s := by
  obtain ⟨A, _, ε, hε, HE⟩ := exists_terminal_coreTail_valid hη hJ
  refine ⟨ε, hε, ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  obtain ⟨hvalid, hT, _, HP⟩ := HE α b u w hα hb hsmall hw
  change coreTailValid h Y at hvalid
  have hR : 1 < Y 0 := by change 1 < 2 + 2 * α; linarith only [hα.1]
  have hh : 0 < h := mul_pos hη.1 (pow_pos hα.1 J)
  have HR (t : ℝ) (ht : t ∈ Icc 0 (coreTailTime h Y)) : exitEntryRegular Y t := by
    have hphys := (HP t ht).2.1
    exact ⟨hR, coreTailValid_denom_pos hvalid, (hvalid.2.1 t ht).1, (hvalid.2.1 t ht).2,
      hh.trans_le hphys.2.2.2.1.1, lt_of_le_of_lt hphys.1 (by norm_num),
      lt_of_lt_of_le (by norm_num) (exitPhysicalRegion_clock hh hphys)⟩
  obtain ⟨U, hUo, hYU, l, r, hl, hr, H⟩ := exists_exitEntry_regular_tube hT.le HR
  have hcover : Icc 0 (coreTailTime h Y) ⊆ Ioo l r :=
    fun _ ht => ⟨hl.trans_le ht.1, ht.2.trans_lt hr⟩
  have h0 := hcover ⟨le_rfl, hT.le⟩
  have ht := hcover ⟨hT.le, le_rfl⟩
  have heh : -Real.log h = S := by
    change -Real.log (η * α ^ J) = exitTailLength η α J
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
  have hS : exitEntryClock (Y, coreTailTime h Y) = S := by
    change -Real.log (coreTailState h Y 2) = S
    rw [coreTailState_active hvalid]
    exact heh
  refine ⟨hvalid, Ioo l r, isOpen_Ioo, convex_Ioo l r, hcover, U, hUo, hYU, H,
    exitClockFlow_initial (convex_Ioo l r) (H Y hYU) h0, ?_, ?_⟩
  · simpa only [heh] using coreTailState_eventuallyEq_exitClockFlow isOpen_Ioo
      (convex_Ioo l r) hUo hYU H hvalid ht
  · intro s hs
    exact exitClockFlow_on_interval isOpen_Ioo (convex_Ioo l r) hUo hYU H hT.le hcover (hS ▸ hs)
