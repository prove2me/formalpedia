-- Prove2me | solution 1 for BianchiIX.exists_terminal_exitClock_multiplier_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:38:46.366027+00:00
-- url     : https://prove2.me/submissions/9b37235e-a1e4-40ca-bc4d-ee72b0d7edbb

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
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
import Theorems.Thm_BianchiIX_contDiffAt_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_exists_exitTail_scale_bounds
import Theorems.Thm_BianchiIX_exists_exitTail_uniform_variation_budget
import Theorems.Thm_BianchiIX_exists_scalar_event_branch_two
import Theorems.Thm_BianchiIX_exists_terminal_exitClock_family
import Theorems.Thm_BianchiIX_exitTailField_jacobian_norm_bound
import Theorems.Thm_BianchiIX_exitTail_boundary_rate_small
import Theorems.Thm_BianchiIX_exitTail_perturbation_bounds
import Theorems.Thm_BianchiIX_exitTail_rate_gradient_bounds
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_hasDerivAt_toExitTailState
import Theorems.Thm_BianchiIX_hasFDerivAt_intervalIntegral_of_contDiffAt
import Theorems.Thm_BianchiIX_homogeneous_solution_eq_exp_integral_Icc
import Theorems.Thm_BianchiIX_integral_exp_decay
import Theorems.Thm_BianchiIX_norm_slope_right_le_of_signedRowSum
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
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem BianchiIX.signedRowSum_sub_scalar {A : Matrix ι ι ℝ} (c : ℝ) (i : ι) :
    signedRowSum (A - c • (1 : Matrix ι ι ℝ)) i = signedRowSum A i - c := by
  have H : (∑ j ∈ Finset.univ.erase i, |(A - c • (1 : Matrix ι ι ℝ)) i j|) =
      ∑ j ∈ Finset.univ.erase i, |A i j| := by
    apply Finset.sum_congr rfl
    intro j hj
    have hij : i ≠ j := Ne.symm (Finset.mem_erase.mp hj).1
    simp [Matrix.sub_apply, Matrix.smul_apply, hij]
  unfold signedRowSum
  rw [H]
  simp [Matrix.sub_apply, Matrix.smul_apply]
  ring

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
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_slope_right_le_of_forced_signedRowSum {f : ℝ → (ι → ℝ)} {t ρ r : ℝ}
    {A : Matrix ι ι ℝ} {q : ι → ℝ} (hf : HasDerivAt f (A.mulVec (f t) + q) t)
    (hA : ∀ i, signedRowSum A i ≤ ρ) (hr : ρ * ‖f t‖ + ‖q‖ < r) :
    ∀ᶠ s in 𝓝[>] t, (s - t)⁻¹ * (‖f s‖ - ‖f t‖) < r := by
  let g : ℝ → (ι → ℝ) := fun s => f s - (s - t) • q
  have hgt : g t = f t := by simp [g]
  have hg : HasDerivAt g (A.mulVec (g t)) t := by
    rw [hgt]
    convert! hf.sub (((hasDerivAt_id t).sub_const t).smul_const q) using 1
    simp
  have H := norm_slope_right_le_of_signedRowSum hg hA
    (r := r - ‖q‖) (by rw [hgt]; linarith only [hr])
  filter_upwards [H, self_mem_nhdsWithin] with s hs hst
  have hh : 0 < s - t := sub_pos.mpr hst
  have hnorm : ‖f s‖ - ‖g s‖ ≤ (s - t) * ‖q‖ := by
    have H' := norm_sub_norm_le (f s) (g s)
    have heq : f s - g s = (s - t) • q := by dsimp [g]; abel
    rwa [heq, norm_smul, Real.norm_eq_abs, abs_of_pos hh] at H'
  have H' := mul_le_mul_of_nonneg_left hnorm (inv_nonneg.mpr hh.le)
  have hid : (s - t)⁻¹ * ((s - t) * ‖q‖) = ‖q‖ := by field_simp
  rw [hid] at H'
  rw [hgt] at hs
  nlinarith only [hs, H']

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_le_of_forced_signedRowSum_nonpos {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ 0)
    (hB : ContinuousOn B (Icc a b)) (hB' : ∀ t ∈ Ico a b, HasDerivAt B (B' t) t)
    (hinit : ‖f a‖ ≤ B a) (hq : ∀ t ∈ Ico a b, ‖q t‖ ≤ B' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ B t := by
  apply image_le_of_liminf_slope_right_le_deriv_boundary
    (continuous_norm.comp_continuousOn hf) hinit hB (fun t ht => (hB' t ht).hasDerivWithinAt)
  intro t ht r hr
  have H := norm_slope_right_le_of_forced_signedRowSum (hderiv t ht) (hA t ht)
    (r := r) (by simpa only [zero_mul, zero_add] using (hq t ht).trans_lt hr)
  simpa only [slope_def_module, smul_eq_mul, Function.comp_apply] using H.frequently

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
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_le_exp_of_forced_budget {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {E E' B B' : ℝ → ℝ} {a b : ℝ}
    (hf : ∀ t ∈ Icc a b, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hE : ∀ t ∈ Icc a b, HasDerivAt E (E' t) t)
    (hA : ∀ t ∈ Icc a b, ∀ i, signedRowSum (A t) i ≤ -E' t)
    (hEa : ∀ t ∈ Icc a b, E t ≤ E a)
    (hB : ∀ t ∈ Icc a b, HasDerivAt B (B' t) t)
    (hinit : ‖f a‖ ≤ B a) (hq : ∀ t ∈ Icc a b, ‖q t‖ ≤ B' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ Real.exp (E a - E t) * B t := by
  let g : ℝ → (ι → ℝ) := fun t => Real.exp (E t) • f t
  let M : ℝ → Matrix ι ι ℝ := fun t => A t - (-E' t) • (1 : Matrix ι ι ℝ)
  let c : ℝ → (ι → ℝ) := fun t => Real.exp (E t) • q t
  have hg (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt g ((M t).mulVec (g t) + c t) t := by
    convert! (hE t ht).exp.smul (hf t ht) using 1
    dsimp [M, g, c]
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hM (t : ℝ) (ht : t ∈ Ico a b) (i : ι) : signedRowSum (M t) i ≤ 0 := by
    dsimp [M]
    rw [signedRowSum_sub_scalar]
    exact sub_nonpos.mpr (hA t (Ico_subset_Icc_self ht) i)
  have hbound (t : ℝ) (ht : t ∈ Icc a b) : ‖c t‖ ≤ Real.exp (E a) * B' t := by
    simp only [c, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact (mul_le_mul_of_nonneg_left (hq t ht) (Real.exp_pos _).le).trans
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (hEa t ht))
        ((norm_nonneg _).trans (hq t ht)))
  have H := norm_le_of_forced_signedRowSum_nonpos (HasDerivAt.continuousOn hg)
    (fun t ht => hg t (Ico_subset_Icc_self ht)) hM
    (HasDerivAt.continuousOn (fun t ht => (hB t ht).const_mul (Real.exp (E a))))
    (fun t ht => (hB t (Ico_subset_Icc_self ht)).const_mul (Real.exp (E a)))
    (by simpa only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
      mul_le_mul_of_nonneg_left hinit (Real.exp_pos (E a)).le)
    (fun t ht => hbound t (Ico_subset_Icc_self ht))
  intro t ht
  have H' := H t ht
  simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at H'
  calc
    ‖f t‖ = Real.exp (-E t) * (Real.exp (E t) * ‖f t‖) := by
      rw [← mul_assoc, ← Real.exp_add, neg_add_cancel, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-E t) * (Real.exp (E a) * B t) :=
      mul_le_mul_of_nonneg_left H' (Real.exp_pos _).le
    _ = Real.exp (E a - E t) * B t := by rw [← mul_assoc, ← Real.exp_add]; congr 2; ring

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_le_integral_envelope_of_forced_budget {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {E E' R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hE : ∀ t ∈ Icc a b, HasDerivAt E (E' t) t)
    (hA : ∀ t ∈ Icc a b, ∀ i, signedRowSum (A t) i ≤ -E' t)
    (hEa : ∀ t ∈ Icc a b, E t ≤ E a) (hR : ContinuousOn R (Icc a b))
    (hq : ∀ t ∈ Icc a b, ‖q t‖ ≤ R t) :
    ‖f b‖ ≤ Real.exp (E a - E b) * (‖f a‖ + ∫ t in a..b, R t) := by
  let r : ℝ → ℝ := fun t => R (projIcc a b hab t)
  have hr : Continuous r := hR.domRestrict.comp continuous_projIcc
  have hre (t : ℝ) (ht : t ∈ Icc a b) : r t = R t := by
    simp only [r, projIcc_of_mem hab ht]
  have hB (t : ℝ) : HasDerivAt (fun s => ‖f a‖ + ∫ u in a..s, r u) (r t) t :=
    (intervalIntegral.integral_hasDerivAt_right (hr.intervalIntegrable _ _)
      hr.stronglyMeasurable.stronglyMeasurableAtFilter hr.continuousAt).const_add _
  have H := norm_le_exp_of_forced_budget hf hE hA hEa (fun t _ => hB t)
    (by simp) (fun t ht => by rw [hre t ht]; exact hq t ht) b ⟨hab, le_rfl⟩
  have heq : (∫ t in a..b, r t) = ∫ t in a..b, R t := by
    apply intervalIntegral.integral_congr
    intro t ht
    exact hre t (uIcc_of_le hab ▸ ht)
  rwa [heq] at H

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
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem BianchiIX.signedRowSum_le_sum_abs (A : Matrix ι ι ℝ) (i : ι) :
    signedRowSum A i ≤ ∑ j, |A i j| := by
  rw [← Finset.add_sum_erase Finset.univ (fun j => |A i j|) (Finset.mem_univ i)]
  exact add_le_add (le_abs_self _) le_rfl

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_le_exp_integral_of_forced_rows {f p : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {σ R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f ((A t).mulVec (f t) + p t) t)
    (hσ : ContinuousOn σ (Icc a b)) (hσ0 : ∀ t ∈ Icc a b, 0 ≤ σ t)
    (hA : ∀ t ∈ Icc a b, ∀ i, signedRowSum (A t) i ≤ σ t)
    (hR : ContinuousOn R (Icc a b)) (hp : ∀ t ∈ Icc a b, ‖p t‖ ≤ R t) :
    ‖f b‖ ≤ Real.exp (∫ t in a..b, σ t) * (‖f a‖ + ∫ t in a..b, R t) := by
  let S : ℝ → ℝ := fun t => σ (projIcc a b hab t)
  let E : ℝ → ℝ := fun t => -(∫ r in a..t, S r)
  have hS : Continuous S := hσ.domRestrict.comp continuous_projIcc
  have hSe (t : ℝ) (ht : t ∈ Icc a b) : S t = σ t := by simp only [S, projIcc_of_mem hab ht]
  have hEe (t : ℝ) (ht : t ∈ Icc a b) : E t = -(∫ r in a..t, σ r) := by
    dsimp only [E]
    congr 1
    apply intervalIntegral.integral_congr
    intro r hr
    exact hSe r ⟨(uIcc_of_le ht.1 ▸ hr).1, (uIcc_of_le ht.1 ▸ hr).2.trans ht.2⟩
  have hE (t : ℝ) (ht : t ∈ Icc a b) : HasDerivAt E (-σ t) t := by
    rw [← hSe t ht]
    exact (intervalIntegral.integral_hasDerivAt_right (hS.intervalIntegrable _ _)
      hS.stronglyMeasurable.stronglyMeasurableAtFilter hS.continuousAt).neg
  have hEa (t : ℝ) (ht : t ∈ Icc a b) : E t ≤ E a := by
    rw [hEe t ht]
    simp only [E, intervalIntegral.integral_same, neg_zero]
    exact neg_nonpos.mpr (intervalIntegral.integral_nonneg ht.1
      (fun r hr => hσ0 r ⟨hr.1, hr.2.trans ht.2⟩))
  have H := norm_le_integral_envelope_of_forced_budget hab hf hE
    (fun t ht i => by simpa only [neg_neg] using hA t ht i) hEa hR hp
  rw [hEe b ⟨hab, le_rfl⟩] at H
  simpa only [E, intervalIntegral.integral_same, neg_zero, zero_sub, neg_neg] using H

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
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Nonempty ι] in
private theorem BianchiIX.signedRowSum_toMatrix_le_opNorm (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) (i : ι) :
    signedRowSum (LinearMap.toMatrix' L.toLinearMap) i ≤ Fintype.card ι * ‖L‖ := by
  apply (signedRowSum_le_sum_abs _ i).trans
  calc
    ∑ j, |LinearMap.toMatrix' L.toLinearMap i j| ≤ ∑ _j : ι, ‖L‖ := by
      apply Finset.sum_le_sum
      intro j _
      have H := (norm_le_pi_norm (L (Pi.single j 1)) i).trans (L.le_opNorm (Pi.single j 1))
      simpa [Pi.norm_single] using H
    _ = _ := by simp

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

private theorem BianchiIX.norm_le_exp_integral_of_forced_linear {f p : ℝ → (ι → ℝ)}
    {L : ℝ → (ι → ℝ) →L[ℝ] (ι → ℝ)} {R : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ∀ t ∈ Icc a b, HasDerivAt f (L t (f t) + p t) t)
    (hL : ContinuousOn L (Icc a b)) (hR : ContinuousOn R (Icc a b))
    (hp : ∀ t ∈ Icc a b, ‖p t‖ ≤ R t) :
    ‖f b‖ ≤ Real.exp (Fintype.card ι * ∫ t in a..b, ‖L t‖) *
      (‖f a‖ + ∫ t in a..b, R t) := by
  have H := norm_le_exp_integral_of_forced_rows hab
    (A := fun t => LinearMap.toMatrix' (L t).toLinearMap)
    (σ := fun t => (Fintype.card ι : ℝ) * ‖L t‖)
    (fun t ht => by simpa using hf t ht)
    (continuousOn_const.mul hL.norm) (fun _ _ => by positivity)
    (fun t _ i => signedRowSum_toMatrix_le_opNorm (L t) i) hR hp
  simpa only [intervalIntegral.integral_const_mul] using H

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
open Set MeasureTheory

private theorem BianchiIX.integral_exp_decay_le {a b c : ℝ} (hc : 0 < c) :
    (∫ z in a..b, Real.exp (-c * (z - a))) ≤ 1 / c := by
  rw [integral_exp_decay hc]
  exact (div_le_div_iff_of_pos_right hc).mpr (by linarith [Real.exp_pos (-c * (b - a))])

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
open Set MeasureTheory

private theorem BianchiIX.integral_exit_tail_envelope {T A B C : ℝ} (hB : 0 ≤ B) (hC : 0 ≤ C) :
    (∫ s in (0 : ℝ)..T, A + B * Real.exp (-s) + C * Real.exp (-2 * s)) ≤ A * T + B + C / 2 := by
  have h0 : IntervalIntegrable (fun _ : ℝ => A) volume 0 T := intervalIntegrable_const
  have h1 : IntervalIntegrable (fun s => B * Real.exp (-s)) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ => B * Real.exp (-s))).intervalIntegrable _ _
  have h2 : IntervalIntegrable (fun s => C * Real.exp (-2 * s)) volume 0 T :=
    (by fun_prop : Continuous (fun s : ℝ => C * Real.exp (-2 * s))).intervalIntegrable _ _
  rw [intervalIntegral.integral_add (h0.add h1) h2, intervalIntegral.integral_add h0 h1,
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have H1 := integral_exp_decay_le (a := 0) (b := T) (by norm_num : (0 : ℝ) < 1)
  have H2 := integral_exp_decay_le (a := 0) (b := T) (by norm_num : (0 : ℝ) < 2)
  simp only [sub_zero, neg_mul, one_mul, one_div_one] at H1 H2
  simp only [sub_zero, smul_eq_mul, neg_mul]
  nlinarith only [mul_le_mul_of_nonneg_left H1 hB, mul_le_mul_of_nonneg_left H2 hC]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_abs_le_exit_tail_envelope {f : ℝ → ℝ} {T A B C : ℝ} (hT : 0 ≤ T)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (hf : ContinuousOn f (Icc 0 T))
    (hbound : ∀ s ∈ Icc 0 T, |f s| ≤ A + B * Real.exp (-s) + C * Real.exp (-2 * s)) :
    (∫ s in (0 : ℝ)..T, |f s|) ≤ A * T + B + C / 2 := by
  have hc : Continuous (fun s : ℝ => A + B * Real.exp (-s) + C * Real.exp (-2 * s)) := by fun_prop
  exact (intervalIntegral.integral_mono_on hT (hf.abs.intervalIntegrable_of_Icc hT)
    (hc.intervalIntegrable _ _) hbound).trans (integral_exit_tail_envelope hB hC)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTailField_wall (v : ℝ) (Y : ExitTailState) (i : Fin 2) :
    exitTailField v Y i.succ = exitTailWallRate v Y i * Y i.succ := by
  fin_cases i <;> rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTailGap {R : ℝ → ℝ} {r s v : ℝ}
    (hR : HasDerivAt R r s) (hv : v ^ 2 < (R s) ^ 2) :
    HasDerivAt (fun q => exitTailGap (R q) v) (R s * r / exitTailGap (R s) v) s := by
  have ht : exitTailGap (R s) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  convert! ((hR.pow 2).sub_const (v ^ 2)).sqrt (ne_of_gt (sub_pos.mpr hv)) using 1
  norm_num only [Nat.reduceSub, pow_one, Pi.pow_apply, Nat.cast_ofNat]
  change R s * r / exitTailGap (R s) v = 2 * R s * r / (2 * exitTailGap (R s) v)
  field_simp

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTail_strongRate {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailStrongRate (Y q 0) (Y q 1) v (Y q 2))
      (∑ i : Fin 3, exitTailStrongRateGradient (Y s 0) (Y s 1) v (Y s 2) i * ξ i) s := by
  have h0 := hasDerivAt_pi.mp hY 0
  have h1 := hasDerivAt_pi.mp hY 1
  have h2 := hasDerivAt_pi.mp hY 2
  have ht := hasDerivAt_exitTailGap h0 hv
  have hc := h1.mul (((hasDerivAt_const s v).add h2).sub h1)
  have hs := ht.add hc
  have hn := (((ht.const_mul 2).sub (h0.pow 2)).add (h2.const_mul (2 * v))).sub (h2.pow 2) |>.add (h1.pow 2)
  have H := hn.div (hs.const_mul 2) (mul_ne_zero (by norm_num) hd)
  apply H.congr_deriv
  have ht0 : exitTailGap (Y s 0) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  simp [Fin.sum_univ_succ, exitTailStrongRateGradient, exitTailStrongRate, exitTailSpeed, coupling]
  dsimp only [exitTailSpeed, coupling] at hd
  field_simp
  ring

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTail_weakRate {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailWeakRate (Y q 0) (Y q 1) v (Y q 2))
      (∑ i : Fin 3, exitTailWeakRateGradient (Y s 0) (Y s 1) v (Y s 2) i * ξ i) s := by
  have h0 := hasDerivAt_pi.mp hY 0
  have h1 := hasDerivAt_pi.mp hY 1
  have h2 := hasDerivAt_pi.mp hY 2
  have ht := hasDerivAt_exitTailGap h0 hv
  have hc := h1.mul (((hasDerivAt_const s v).add h2).sub h1)
  have hs := ht.add hc
  have H := ((ht.sub_const 2).sub hc).div hs hd
  apply H.congr_deriv
  have ht0 : exitTailGap (Y s 0) v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (sub_pos.mpr hv))
  simp [Fin.sum_univ_succ, exitTailWeakRateGradient, exitTailWeakRate, exitTailSpeed, coupling]
  dsimp only [exitTailSpeed, coupling] at hd
  field_simp
  ring

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
open Set MeasureTheory

private theorem BianchiIX.exitTailWallRate_abs {α v : ℝ} {Y : ExitTailState} (hα : 0 ≤ α)
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (i : Fin 2) :
    |exitTailWallRate v Y i| ≤ 10 * (α + |Y 0 - (2 + 2 * α)| + v ^ 2) +
      100 * ((|Y 1| + |Y 2|) * v + (|Y 1| + |Y 2|) ^ 2) := by
  have Hp := exitTail_perturbation_bounds hR hu hv hw
  have Hb := exitTail_boundary_rate_small hα hR hv
  fin_cases i
  · change |exitTailStrongRate (Y 0) (Y 1) v (Y 2)| ≤ _
    have H := abs_sub_le (exitTailStrongRate (Y 0) (Y 1) v (Y 2)) (exitTailStrongRate (Y 0) 0 v 0) 0
    simp only [sub_zero] at H
    linarith only [H, Hp.2.1, Hb, abs_nonneg (exitTailWeakRate (Y 0) 0 v 0)]
  · change |exitTailWeakRate (Y 0) (Y 1) v (Y 2)| ≤ _
    have H := abs_sub_le (exitTailWeakRate (Y 0) (Y 1) v (Y 2)) (exitTailWeakRate (Y 0) 0 v 0) 0
    simp only [sub_zero] at H
    linarith only [H, Hp.2.2, Hb, abs_nonneg (exitTailStrongRate (Y 0) 0 v 0)]

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.contDiffAt_exitTail_stateDerivative (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hR : Y 0 ≠ 0)
    (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => fderiv ℝ (exitTailField q.1) q.2) (v, Y) := by
  have hmap : ContDiffAt ℝ (n + 1)
      (fun q : (ℝ × ExitTailState) × ExitTailState => (q.1.1, q.2)) ((v, Y), Y) := by fun_prop
  have H := contDiffAt_exitTailField (n + 1) hv hR hd
  have HF := H.comp ((v, Y), Y) hmap
  exact HF.fderiv (f := fun q : ℝ × ExitTailState => exitTailField q.1) contDiffAt_snd le_rfl

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailRateGradient_bounds {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (i : Fin 2) :
    |exitTailRateGradient v Y i 0| ≤ 512 ∧
      ∀ j : Fin 2, |exitTailRateGradient v Y i j.succ| ≤ 256 * (v + |Y 1| + |Y 2|) := by
  have H := exitTail_rate_gradient_bounds hR hu hv hw
  fin_cases i
  · exact ⟨H.1, fun j => (H.2.2 j).1⟩
  · exact ⟨H.2.1, fun j => (H.2.2 j).2⟩

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.contDiffAt_exitTailWallRate (n : WithTop ℕ∞) {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0) :
    ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailWallRate q.1 q.2) (v, Y) := by
  have hcoord (i : Fin 3) : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => q.2 i) (v, Y) := by fun_prop
  have ht : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailGap (q.2 0) q.1) (v, Y) := by
    unfold exitTailGap
    exact (((hcoord 0).pow 2).sub (contDiffAt_fst.pow 2)).sqrt (ne_of_gt (sub_pos.mpr hv))
  have hc : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => coupling (q.2 1) q.1 (q.2 2)) (v, Y) := by
    unfold coupling
    fun_prop
  have hs : ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailSpeed (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y) :=
    ht.add hc
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailStrongRate (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y)
    exact (((((contDiffAt_const.mul ht).sub ((hcoord 0).pow 2)).add
      ((contDiffAt_const.mul contDiffAt_fst).mul (hcoord 2))).sub ((hcoord 2).pow 2)).add ((hcoord 1).pow 2)).div
      (contDiffAt_const.mul hs) (mul_ne_zero (by norm_num) hd)
  · change ContDiffAt ℝ n (fun q : ℝ × ExitTailState => exitTailWeakRate (q.2 0) (q.2 1) q.1 (q.2 2)) (v, Y)
    exact ((ht.sub contDiffAt_const).sub hc).div hs hd

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.hasDerivAt_exitTailWallRate {Y : ℝ → ExitTailState} {ξ : ExitTailState} {s v : ℝ}
    (hY : HasDerivAt Y ξ s) (hv : v ^ 2 < (Y s 0) ^ 2)
    (hd : exitTailSpeed (Y s 0) (Y s 1) v (Y s 2) ≠ 0) :
    HasDerivAt (fun q => exitTailWallRate v (Y q))
      (fun i => ∑ j : Fin 3, exitTailRateGradient v (Y s) i j * ξ j) s := by
  apply hasDerivAt_pi.mpr
  intro i
  fin_cases i
  · exact hasDerivAt_exitTail_strongRate hY hv hd
  · exact hasDerivAt_exitTail_weakRate hY hv hd

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailWallRate_fderiv {v : ℝ} {Y : ExitTailState}
    (hv : v ^ 2 < (Y 0) ^ 2) (hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0)
    (ξ : ExitTailState) (i : Fin 2) :
    fderiv ℝ (exitTailWallRate v) Y ξ i = ∑ j : Fin 3, exitTailRateGradient v Y i j * ξ j := by
  have hreg : ContDiffAt ℝ 1 (exitTailWallRate v) Y :=
    (contDiffAt_exitTailWallRate 1 hv hd).comp Y (by fun_prop)
  have hline : HasDerivAt (fun s : ℝ => Y + s • ξ) ξ 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const ξ).const_add Y
  have hf : HasFDerivAt (exitTailWallRate v) (fderiv ℝ (exitTailWallRate v) Y) (Y + (0 : ℝ) • ξ) := by
    simpa using (hreg.differentiableAt (by norm_num)).hasFDerivAt
  have H := hf.comp_hasDerivAt 0 hline
  have K := hasDerivAt_exitTailWallRate hline (by simpa using hv) (by simpa using hd)
  simpa only [zero_smul, add_zero] using congrFun (H.unique K) i

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.continuousOn_exitTail_stateDerivative {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hY : ContinuousOn Y (Icc 0 T)) (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) :
    ContinuousOn (fun s => fderiv ℝ (exitTailField (Real.exp (-s))) (Y s)) (Icc 0 T) := by
  have hpair : ContinuousOn (fun s => (Real.exp (-s), Y s)) (Icc 0 T) :=
    (by fun_prop : ContinuousOn (fun s : ℝ => Real.exp (-s)) (Icc 0 T)).prodMk hY
  intro s hs
  have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
  have hR := (hreg s hs).1
  have hvR : Real.exp (-s) ^ 2 < (Y s 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hR0 : Y s 0 ≠ 0 := by linarith only [hR.1]
  have hd : exitTailSpeed (Y s 0) (Y s 1) (Real.exp (-s)) (Y s 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 (hreg s hs).2.1 hv (hreg s hs).2.2.1
    linarith only [H]
  have H := (contDiffAt_exitTail_stateDerivative 0 hvR hR0 hd).continuousAt
  exact H.comp_continuousWithinAt
    (f := fun r : ℝ => (Real.exp (-r), Y r)) (hpair s hs)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTail_jacobian_integral_bound {Y : ℝ → ExitTailState} {T α b A D : ℝ}
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) :
    (∫ s in (0 : ℝ)..T, ‖fderiv ℝ (exitTailField (Real.exp (-s))) (Y s)‖) ≤
      2 * exitTailRateBudget α b A D T + 2048 * (1 + A * b * T) := by
  let a := 20 * (α + D * b) + 200 * (A * b) ^ 2 + 2048 * A * b
  let c := 200 * A * b + 2048
  have hc : 0 ≤ c := by dsimp only [c]; positivity
  have hcontinuous := (continuousOn_exitTail_stateDerivative hY hreg).norm
  have HE := integral_abs_le_exit_tail_envelope hT hc (by norm_num : (0 : ℝ) ≤ 20)
    hcontinuous (A := a) ?_
  · have H : (∫ s in (0 : ℝ)..T, ‖fderiv ℝ (exitTailField (Real.exp (-s))) (Y s)‖) ≤
        a * T + c + 20 / 2 := by simpa only [abs_norm] using HE
    apply H.trans_eq
    dsimp only [a, c, exitTailRateBudget]
    ring
  · intro s hs
    rw [abs_norm]
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    obtain ⟨hR, hu, hw, hsum, hrad⟩ := hreg s hs
    have H0 := exitTailWallRate_abs hα hR hu hv hw 0
    have H1 := exitTailWallRate_abs hα hR hu hv hw 1
    have HJ := exitTailField_jacobian_norm_bound hR hu hv hw
    have hsq := (sq_le_sq₀ (add_nonneg (abs_nonneg _) (abs_nonneg _)) (mul_nonneg hA hb)).mpr hsum
    have hm := mul_le_mul_of_nonneg_right hsum hv.1
    have he : Real.exp (-s) ^ 2 = Real.exp (-2 * s) := by
      rw [sq, ← Real.exp_add]
      congr 1
      ring
    rw [he] at H0 H1
    dsimp only [a, c]
    nlinarith only [H0, H1, HJ, hsq, hm, hrad, hsum]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailWallRate_direction_bound {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (ξ : ExitTailState) (i : Fin 2) :
    |fderiv ℝ (exitTailWallRate v) Y ξ i| ≤
      512 * |ξ 0| + 256 * (v + |Y 1| + |Y 2|) * (|ξ 1| + |ξ 2|) := by
  have hvR : v ^ 2 < (Y 0) ^ 2 := by nlinarith only [hR.1, hv.1, hv.2]
  have hd : exitTailSpeed (Y 0) (Y 1) v (Y 2) ≠ 0 := by
    have H := exitTailSpeed_compact hR.1 hu hv hw
    linarith only [H]
  rw [exitTailWallRate_fderiv hvR hd, Fin.sum_univ_three]
  have HG := exitTailRateGradient_bounds hR hu hv hw i
  have H0 := mul_le_mul_of_nonneg_right HG.1 (abs_nonneg (ξ 0))
  have H1 := mul_le_mul_of_nonneg_right (HG.2 0) (abs_nonneg (ξ 1))
  have H2 := mul_le_mul_of_nonneg_right (HG.2 1) (abs_nonneg (ξ 2))
  have H := abs_add_three (exitTailRateGradient v Y i 0 * ξ 0)
    (exitTailRateGradient v Y i 1 * ξ 1) (exitTailRateGradient v Y i 2 * ξ 2)
  simp only [abs_mul] at H
  change |exitTailRateGradient v Y i 1| * |ξ 1| ≤ _ at H1
  change |exitTailRateGradient v Y i 2| * |ξ 2| ≤ _ at H2
  nlinarith only [H, H0, H1, H2]

end
end

section
noncomputable section
open BianchiIX

private theorem BianchiIX.exitTailWallRate_direction_norm_bound {v : ℝ} {Y : ExitTailState}
    (hR : 7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) (hu : |Y 1| ≤ 1 / 100)
    (hv : 0 ≤ v ∧ v ≤ 1) (hw : |Y 2| ≤ 1 / 100) (ξ : ExitTailState) (i : Fin 2) :
    |fderiv ℝ (exitTailWallRate v) Y ξ i| ≤ 1536 * ‖ξ‖ := by
  have H := exitTailWallRate_direction_bound hR hu hv hw ξ i
  have hξ (j : Fin 3) : |ξ j| ≤ ‖ξ‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm ξ j
  have hp : 256 * (v + |Y 1| + |Y 2|) ≤ 512 := by linarith only [hv.2, hu, hw]
  have hm := mul_le_mul_of_nonneg_right hp (add_nonneg (abs_nonneg (ξ 1)) (abs_nonneg (ξ 2)))
  nlinarith only [H, hm, hξ 0, hξ 1, hξ 2]

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTail_jacobian_subinterval_bound {Y : ℝ → ExitTailState} {T α b A D a t : ℝ}
    (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s))
    (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ T) :
    (∫ s in a..t, ‖fderiv ℝ (exitTailField (Real.exp (-s))) (Y s)‖) ≤
      exitTailVariationBudget α b A D T := by
  have hc := (continuousOn_exitTail_stateDerivative hY hreg).norm
  apply le_trans (intervalIntegral.integral_mono_interval ha hat ht
    (Filter.Eventually.of_forall (fun s => norm_nonneg _)) (hc.intervalIntegrable_of_Icc hT))
  exact exitTail_jacobian_integral_bound hT hα hb hA hY hreg

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTail_forced_variation_bound {Y X P : ℝ → ExitTailState} {R : ℝ → ℝ}
    {T α b A D a t : ℝ} (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s))
    (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ T)
    (hX : ∀ s ∈ Icc a t, HasDerivAt X
      (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s) + P s) s)
    (hR : ContinuousOn R (Icc a t)) (hP : ∀ s ∈ Icc a t, ‖P s‖ ≤ R s) :
    ‖X t‖ ≤ Real.exp (3 * exitTailVariationBudget α b A D T) *
      (‖X a‖ + ∫ s in a..t, R s) := by
  have hsub : Icc a t ⊆ Icc 0 T := fun _ hs => ⟨ha.trans hs.1, hs.2.trans ht⟩
  have H := norm_le_exp_integral_of_forced_linear hat hX
    ((continuousOn_exitTail_stateDerivative hY hreg).mono hsub) hR hP
  have HB := exitTail_jacobian_subinterval_bound hT hα hb hA hY hreg ha hat ht
  have hRn : 0 ≤ ∫ s in a..t, R s := intervalIntegral.integral_nonneg hat
    (fun s hs => (norm_nonneg _).trans (hP s hs))
  apply H.trans
  apply mul_le_mul_of_nonneg_right _ (add_nonneg (norm_nonneg _) hRn)
  apply Real.exp_le_exp.mpr
  simpa using mul_le_mul_of_nonneg_left HB (by norm_num : (0 : ℝ) ≤ 3)

end
end

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.exitTail_variation_bound {Y X : ℝ → ExitTailState}
    {T α b A D a t : ℝ} (hT : 0 ≤ T) (hα : 0 ≤ α) (hb : 0 ≤ b) (hA : 0 ≤ A)
    (hY : ContinuousOn Y (Icc 0 T))
    (hreg : ∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s))
    (ha : 0 ≤ a) (hat : a ≤ t) (ht : t ≤ T)
    (hX : ∀ s ∈ Icc a t, HasDerivAt X
      (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s)) s) :
    ‖X t‖ ≤ Real.exp (3 * exitTailVariationBudget α b A D T) * ‖X a‖ := by
  simpa using exitTail_forced_variation_bound hT hα hb hA hY hreg ha hat ht
    (P := fun _ => 0) (R := fun _ => 0) (fun s hs => by simpa using hX s hs)
    continuousOn_const (fun _ _ => by simp)

end
end

section
noncomputable section
open BianchiIX
open Set

private theorem BianchiIX.exists_exitTail_uniform_linear_bound {η : ℝ} (hη : 0 < η ∧ η ≤ 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ (α b T : ℝ) (Y : ℝ → ExitTailState),
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      (0 ≤ T ∧ T ≤ exitTailLength η α J) → Y 0 0 = 2 + 2 * α →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      ∀ (X : ℝ → ExitTailState) (a t : ℝ), 0 ≤ a → a ≤ t → t ≤ T →
      (∀ s ∈ Icc a t, HasDerivAt X
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s)) s) → ‖X t‖ ≤ C * ‖X a‖ := by
  obtain ⟨A, hA, B, hB, ε, hε, H⟩ := exists_exitTail_uniform_variation_budget hη hJ
  refine ⟨Real.exp (3 * B), Real.one_le_exp_iff.mpr (by positivity), ε, hε, ?_⟩
  intro α b T Y hα hb hsmall hT hR hw hY X a t ha hat ht hX
  obtain ⟨hreg, hbudget⟩ := H α b T Y hα hb hsmall hT hR hw hY
  apply (exitTail_variation_bound hT.1 hα.1.le hb.le (by linarith only [hA])
    (HasDerivAt.continuousOn hY) hreg ha hat ht hX).trans
  apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (by norm_num))

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
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.contDiffAt_exitClockRateIntegrand {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hΦ : ContDiffAt ℝ 1 (exitClockFlow I) (Y, s))
    (hv : (Real.exp (-s)) ^ 2 < (exitClockFlow I (Y, s) 0) ^ 2)
    (hd : exitTailSpeed (exitClockFlow I (Y, s) 0) (exitClockFlow I (Y, s) 1)
      (Real.exp (-s)) (exitClockFlow I (Y, s) 2) ≠ 0) (i : Fin 2) :
    ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Y, s) := by
  have hmap : ContDiffAt ℝ 1 (fun p : ExitTailState × ℝ => (Real.exp (-p.2), exitClockFlow I p)) (Y, s) :=
    (contDiffAt_snd.neg.exp).prodMk hΦ
  have HR := (contDiffAt_exitTailWallRate 1 hv hd).comp (Y, s) hmap
  exact contDiffAt_pi.mp HR i

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.exitClockRateIntegrand_partial {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hΦ : ContDiffAt ℝ 1 (exitClockFlow I) (Y, s))
    (hv : (Real.exp (-s)) ^ 2 < (exitClockFlow I (Y, s) 0) ^ 2)
    (hd : exitTailSpeed (exitClockFlow I (Y, s) 0) (exitClockFlow I (Y, s) 1)
      (Real.exp (-s)) (exitClockFlow I (Y, s) 2) ≠ 0) (i : Fin 2) (v : ExitTailState) :
    fderiv ℝ (exitClockRateIntegrand I i) (Y, s) (v, 0) =
      fderiv ℝ (exitTailWallRate (Real.exp (-s))) (exitClockFlow I (Y, s))
        (fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y v) i := by
  have hFs : HasFDerivAt (fun Z => exitClockFlow I (Z, s))
      (fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y) Y := by
    have HF := hΦ.comp Y (contDiffAt_id.prodMk (contDiffAt_const (c := s)))
    exact (HF.differentiableAt (by norm_num)).hasFDerivAt
  have hAs : ContDiffAt ℝ 1 (exitTailWallRate (Real.exp (-s))) (exitClockFlow I (Y, s)) := by
    have HA := (contDiffAt_exitTailWallRate 1 hv hd).comp (exitClockFlow I (Y, s))
      ((contDiffAt_const (c := Real.exp (-s))).prodMk contDiffAt_id)
    exact HA
  have HA := (hasFDerivAt_pi'.mp (hAs.differentiableAt (by norm_num)).hasFDerivAt i).comp Y hFs
  have HP := ((contDiffAt_exitClockRateIntegrand hΦ hv hd i).differentiableAt
    (by norm_num)).hasFDerivAt.comp Y (hasFDerivAt_prodMk_left (𝕜 := ℝ) Y s)
  exact congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v) (HP.unique HA)

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.exitClockLogMultiplier_regular {I : Set ℝ} {Y : ExitTailState} {s : ℝ}
    (hs : 0 ≤ s) (i : Fin 2)
    (H : ∀ r ∈ Icc 0 s, ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Y, r)) :
    ContDiffAt ℝ 1 (fun Z => exitClockLogMultiplier I i Z s) Y ∧
      fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y =
        ∫ r in (0 : ℝ)..s, (fderiv ℝ (exitClockRateIntegrand I i) (Y, r)).comp
          (ContinuousLinearMap.inl ℝ ExitTailState ℝ) := by
  exact ⟨contDiffAt_intervalIntegral_of_contDiffAt hs H,
    (hasFDerivAt_intervalIntegral_of_contDiffAt hs H).fderiv⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter MeasureTheory
open scoped Topology

private theorem BianchiIX.exitClockLogMultiplier_derivative_bound {I : Set ℝ} {Y : ExitTailState} {s K : ℝ}
    (hs : 0 ≤ s) (hK : 0 ≤ K)
    (hΦ : ∀ r ∈ Icc 0 s, ContDiffAt ℝ 1 (exitClockFlow I) (Y, r))
    (hreg : ∀ r ∈ Icc 0 s, (7 / 4 ≤ exitClockFlow I (Y, r) 0 ∧ exitClockFlow I (Y, r) 0 ≤ 17 / 4) ∧
      |exitClockFlow I (Y, r) 1| ≤ 1 / 100 ∧ |exitClockFlow I (Y, r) 2| ≤ 1 / 100)
    (hbound : ∀ r ∈ Icc 0 s, ‖fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y‖ ≤ K) (i : Fin 2) :
    ContDiffAt ℝ 1 (fun Z => exitClockLogMultiplier I i Z s) Y ∧
      ‖fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y‖ ≤ 1536 * K * s := by
  have hv (r : ℝ) (hr : r ∈ Icc 0 s) : 0 ≤ Real.exp (-r) ∧ Real.exp (-r) ≤ 1 :=
    ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hr.1)⟩
  have hsep (r : ℝ) (hr : r ∈ Icc 0 s) :
      (Real.exp (-r)) ^ 2 < (exitClockFlow I (Y, r) 0) ^ 2 := by
    have HR := (hreg r hr).1.1
    nlinarith only [HR, (hv r hr).1, (hv r hr).2]
  have hd (r : ℝ) (hr : r ∈ Icc 0 s) :
      exitTailSpeed (exitClockFlow I (Y, r) 0) (exitClockFlow I (Y, r) 1)
        (Real.exp (-r)) (exitClockFlow I (Y, r) 2) ≠ 0 := by
    have H := exitTailSpeed_compact (hreg r hr).1.1 (hreg r hr).2.1 (hv r hr) (hreg r hr).2.2
    linarith only [H]
  obtain ⟨HC, HD⟩ := exitClockLogMultiplier_regular hs i
    (fun r hr => contDiffAt_exitClockRateIntegrand (hΦ r hr) (hsep r hr) (hd r hr) i)
  refine ⟨HC, ?_⟩
  rw [HD]
  have HI := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := 0) (b := s) (C := 1536 * K)
    (f := fun r => (fderiv ℝ (exitClockRateIntegrand I i) (Y, r)).comp
      (ContinuousLinearMap.inl ℝ ExitTailState ℝ)) ?_
  · simpa only [sub_zero, abs_of_nonneg hs] using HI
  · intro r hr
    have hr' : r ∈ Icc 0 s := uIcc_of_le hs ▸ uIoc_subset_uIcc hr
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro v
    change |fderiv ℝ (exitClockRateIntegrand I i) (Y, r) (v, 0)| ≤ _
    rw [exitClockRateIntegrand_partial (hΦ r hr') (hsep r hr') (hd r hr') i v]
    have H := exitTailWallRate_direction_norm_bound (hreg r hr').1 (hreg r hr').2.1
      (hv r hr') (hreg r hr').2.2 (fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y v) i
    have HV := ((fderiv ℝ (fun Z => exitClockFlow I (Z, r)) Y).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right (hbound r hr') (norm_nonneg v))
    exact H.trans (by nlinarith only [HV])

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.contDiffAt_exitClockRateIntegrand_graph {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {Y : ExitTailState} {t : ℝ} (ht : t ∈ I)
    (H : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r) (i : Fin 2) :
    ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Y, exitEntryClock (Y, t)) := by
  have HR := H.self_of_nhds t ht
  have he := exitClockFlow_eq hI H.self_of_nhds ht
  have hv : (Real.exp (-exitEntryClock (Y, t))) ^ 2 <
      (exitClockFlow I (Y, exitEntryClock (Y, t)) 0) ^ 2 := by
    rw [he]
    change (Real.exp (-exitLogClock (exitEntryFlow (Y, t)))) ^ 2 <
      coreRadius (exitEntryFlow (Y, t) 0) (exitEntryFlow (Y, t) 2) ^ 2
    rw [exp_neg_exitLogClock HR.2.2.2.2.1, coreRadius_sq]
    dsimp only [coreEnergy]
    nlinarith only [sq_pos_of_neg (sub_neg.mpr HR.2.2.2.2.2.1)]
  have hd : exitTailSpeed (exitClockFlow I (Y, exitEntryClock (Y, t)) 0)
      (exitClockFlow I (Y, exitEntryClock (Y, t)) 1) (Real.exp (-exitEntryClock (Y, t)))
      (exitClockFlow I (Y, exitEntryClock (Y, t)) 2) ≠ 0 := by
    rw [he]
    change exitTailSpeed (coreRadius (exitEntryFlow (Y, t) 0) (exitEntryFlow (Y, t) 2))
      (exitEntryFlow (Y, t) 1) (Real.exp (-exitLogClock (exitEntryFlow (Y, t)))) (exitEntryFlow (Y, t) 3) ≠ 0
    rw [exp_neg_exitLogClock HR.2.2.2.2.1, ← exitClockRate_tail HR.2.2.2.2.2.1]
    exact HR.2.2.2.2.2.2.ne'
  exact contDiffAt_exitClockRateIntegrand
    ((contDiffAt_exitClockFlow_two hIo hI ht H).of_le (by norm_num)) hv hd i

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockFlow_near_wall_equation {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T s : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) (i : Fin 2) :
    ∀ᶠ Z in 𝓝 Y, ∀ r ∈ Icc 0 s,
      ContDiffAt ℝ 1 (exitClockRateIntegrand I i) (Z, r) ∧
      HasDerivAt (fun a => exitClockFlow I (Z, a))
        (exitTailField (Real.exp (-r)) (exitClockFlow I (Z, r))) r := by
  have HY : ∀ᶠ Z in 𝓝 Y, ∀ r ∈ I, exitEntryRegular Z r := by
    filter_upwards [hUo.mem_nhds hY] with Z hZ
    exact H Z hZ
  apply isCompact_Icc.eventually_forall_of_forall_eventually
  intro r hr
  obtain ⟨t, ht, he⟩ := exitEntryClock_interval_surjective hT
    (fun t ht => H Y hY t (hcover ht)) ⟨hr.1, hr.2.trans hs.2⟩
  have HA := (contDiffAt_exitClockRateIntegrand_graph hIo hI (hcover ht) HY i).eventually (by norm_num)
  have HF := exitClockFlow_local_ode hIo hI hUo hY H (hcover ht)
  rw [he] at HA HF
  filter_upwards [HA, HF] with p hp hpf
  exact ⟨hp, hpf.2⟩

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockFlow_eventually_wall_factor {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T s : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) (i : Fin 2) :
    (fun Z => exitClockFlow I (Z, s) i.succ) =ᶠ[𝓝 Y]
      (fun Z => Z i.succ * Real.exp (exitClockLogMultiplier I i Z s)) := by
  filter_upwards [exitClockFlow_near_wall_equation hIo hI hUo hY H hT hcover hs i,
    hUo.mem_nhds hY] with Z hZ hZU
  have hrate : ContinuousOn (fun r => exitClockRateIntegrand I i (Z, r)) (Icc 0 s) :=
    fun r hr => ((hZ r hr).1.continuousAt.comp (continuousAt_const.prodMk continuousAt_id)).continuousWithinAt
  have hwall (r : ℝ) (hr : r ∈ Icc 0 s) : HasDerivAt (fun a => exitClockFlow I (Z, a) i.succ)
      (exitClockRateIntegrand I i (Z, r) * exitClockFlow I (Z, r) i.succ) r := by
    have HD := hasDerivAt_pi.mp (hZ r hr).2 i.succ
    rwa [exitTailField_wall] at HD
  have HF := homogeneous_solution_eq_exp_integral_Icc hs.1 hrate (HasDerivAt.continuousOn hwall)
    (fun r hr => hwall r (Ioo_subset_Icc_self hr))
  rw [exitClockFlow_initial hI (H Z hZU) (hcover ⟨le_rfl, hT⟩)] at HF
  exact HF

end
end

section
noncomputable section
open BianchiIX
open Set Filter
open scoped Topology

private theorem BianchiIX.exitClockFlow_wall_differential {I : Set ℝ} (hIo : IsOpen I) (hI : Convex ℝ I)
    {U : Set ExitTailState} (hUo : IsOpen U) {Y : ExitTailState} (hY : Y ∈ U)
    (H : ∀ Z ∈ U, ∀ r ∈ I, exitEntryRegular Z r) {T s : ℝ} (hT : 0 ≤ T)
    (hcover : Icc 0 T ⊆ I) (hs : s ∈ Icc 0 (exitEntryClock (Y, T))) (i : Fin 2) (v : ExitTailState) :
    fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y v i.succ =
      Real.exp (exitClockLogMultiplier I i Y s) * v i.succ +
        exitClockFlow I (Y, s) i.succ * fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y v := by
  have Hnear := exitClockFlow_near_wall_equation hIo hI hUo hY H hT hcover hs i
  have hL := (exitClockLogMultiplier_regular hs.1 i (fun r hr => (Hnear.self_of_nhds r hr).1)).1
  have hΦ := (exitClockFlow_on_interval hIo hI hUo hY H hT hcover hs).1
  have hslice := hΦ.comp Y (contDiffAt_id.prodMk (contDiffAt_const (c := s)))
  have HS := hasFDerivAt_pi'.mp (hslice.differentiableAt (by norm_num)).hasFDerivAt i.succ
  have HE := exitClockFlow_eventually_wall_factor hIo hI hUo hY H hT hcover hs i
  have HD := (hasFDerivAt_apply (𝕜 := ℝ) i.succ Y).mul
    ((hL.differentiableAt (by norm_num)).hasFDerivAt.exp)
  have HV := congrArg (fun L : ExitTailState →L[ℝ] ℝ => L v)
    ((HS.congr_of_eventuallyEq HE.symm).unique HD)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, add_apply,
    smul_apply, smul_eq_mul, Function.comp_def, id_eq] at HV
  have Hval : exitClockFlow I (Y, s) i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y s) :=
    HE.self_of_nhds
  rw [Hval]
  nlinarith only [HV]

end
end


/-- Actual wall multipliers and their ordinary logarithmic derivatives, uniformly along the terminal flight. -/
theorem solution {η : ℝ} (hη : 0 < η ∧ η < 1) {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ α b u w : ℝ,
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      let S := exitTailLength η α J
      coreTailValid h Y ∧ ∃ I : Set ℝ, IsOpen I ∧ Convex ℝ I ∧ Icc 0 (coreTailTime h Y) ⊆ I ∧
        ∃ U : Set ExitTailState, IsOpen U ∧ Y ∈ U ∧ (∀ Z ∈ U, ∀ t ∈ I, exitEntryRegular Z t) ∧
        exitClockFlow I (Y, 0) = Y ∧
        ((fun Z => toExitTailState (coreTailState h Z)) =ᶠ[𝓝 Y] (fun Z => exitClockFlow I (Z, S))) ∧
        ∀ s ∈ Icc 0 S, ContDiffAt ℝ 2 (exitClockFlow I) (Y, s) ∧
          ‖fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y‖ ≤ C ∧
          (∀ i : Fin 2,
            exitClockFlow I (Y, s) i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y s) ∧
            ContDiffAt ℝ 1 (fun Z => exitClockLogMultiplier I i Z s) Y ∧
            1 / C ≤ Real.exp (exitClockLogMultiplier I i Y s) ∧
            Real.exp (exitClockLogMultiplier I i Y s) ≤ C ∧
            ∀ v : ExitTailState,
              fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y v i.succ =
                Real.exp (exitClockLogMultiplier I i Y s) * v i.succ +
                exitClockFlow I (Y, s) i.succ * fderiv ℝ (fun Z => exitClockLogMultiplier I i Z s) Y v) ∧
          ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 0 Z s) Y‖ +
            ‖fderiv ℝ (fun Z => exitClockLogMultiplier I 1 Z s) Y‖ ≤ C * s := by
  obtain ⟨εe, hεe, HE⟩ := exists_terminal_exitClock_family hη hJ
  obtain ⟨A, hA, ε₀, hε₀, H₀⟩ := exists_exitTail_scale_bounds ⟨hη.1, hη.2.le⟩ hJ
  obtain ⟨K, hK, ε₁, hε₁, H₁⟩ := exists_exitTail_uniform_linear_bound ⟨hη.1, hη.2.le⟩ hJ
  let C := A + 3072 * K
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hA, hK]
  have hC0 : 0 < C := lt_of_lt_of_le (by norm_num) hC
  have hAC : A ≤ C := by dsimp only [C]; linarith only [hK]
  have hKC : K ≤ C := by dsimp only [C]; linarith only [hA, hK]
  have hDC : 3072 * K ≤ C := by dsimp only [C]; linarith only [hA]
  have hA0 : 0 < A := by linarith only [hA]
  let ε := min εe (min ε₀ ε₁)
  refine ⟨C, hC, ε, lt_min hεe (lt_min hε₀ hε₁), ?_⟩
  intro α b u w hα hb hsmall hw Y h S
  have he := hsmall.trans (mul_le_mul_of_nonneg_right (min_le_left εe (min ε₀ ε₁)) (pow_nonneg hα.1.le J))
  have hb₀ := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εe (min ε₀ ε₁)).trans (min_le_left ε₀ ε₁)) (pow_nonneg hα.1.le J))
  have hb₁ := hsmall.trans (mul_le_mul_of_nonneg_right
    ((min_le_right εe (min ε₀ ε₁)).trans (min_le_right ε₀ ε₁)) (pow_nonneg hα.1.le J))
  obtain ⟨hvalid, I, hIo, hI, hcover, U, hUo, hYU, HR, hinit, hend, HF⟩ := HE α b u w hα hb he hw
  change coreTailValid h Y at hvalid
  have hT : 0 ≤ coreTailTime h Y := hvalid.1.1.1.le
  have hS : 0 ≤ S := exitTailLength_nonneg ⟨hη.1, hη.2.le⟩ hα J
  have hclock : exitEntryClock (Y, coreTailTime h Y) = S := by
    change -Real.log (coreTailState h Y 2) = S
    rw [coreTailState_active hvalid]
    change -Real.log (η * α ^ J) = exitTailLength η α J
    rw [← exp_neg_exitTailLength hη.1 hα.1 J, Real.log_exp, neg_neg]
  let β : ℝ → ExitTailState := fun s => exitClockFlow I (Y, s)
  have hβ0 : β 0 = Y := hinit
  have hR : β 0 0 = 2 + 2 * α := by rw [hβ0]; rfl
  have hwall : |β 0 1| + |β 0 2| ≤ b := by rw [hβ0]; exact hw
  have hβ (s : ℝ) (hs : s ∈ Icc 0 S) : HasDerivAt β (exitTailField (Real.exp (-s)) (β s)) s :=
    (HF s hs).2.1
  have HP := H₀ α b S β hα hb hb₀ ⟨hS, le_rfl⟩ hR hwall hβ
  have hnorm (s : ℝ) (hs : s ∈ Icc 0 S) : ‖fderiv ℝ (fun Z => exitClockFlow I (Z, s)) Y‖ ≤ K := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by linarith only [hK])
    intro v
    rw [fderiv_parameterSlice_apply ((HF s hs).1.differentiableAt (by norm_num)) v]
    have HB := H₁ α b S β hα hb hb₁ ⟨hS, le_rfl⟩ hR hwall hβ
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0)) 0 s le_rfl hs.1 hs.2
      (fun r hr => (HF r ⟨hr.1, hr.2.trans hs.2⟩).2.2 v)
    rwa [exitClockFlow_variation_initial hIo hI hUo hYU HR (hcover ⟨le_rfl, hT⟩) v] at HB
  refine ⟨hvalid, I, hIo, hI, hcover, U, hUo, hYU, HR, hinit, hend, ?_⟩
  intro s hs
  have hsub : Icc 0 s ⊆ Icc 0 S := fun _ hr => ⟨hr.1, hr.2.trans hs.2⟩
  have HL (i : Fin 2) := exitClockLogMultiplier_derivative_bound hs.1 (by linarith only [hK] : 0 ≤ K)
    (fun r hr => (HF r (hsub hr)).1.of_le (by norm_num))
    (fun r hr => ⟨(HP r (hsub hr)).1.1, (HP r (hsub hr)).1.2.1, (HP r (hsub hr)).1.2.2.1⟩)
    (fun r hr => hnorm r (hsub hr)) i
  refine ⟨(HF s hs).1, (hnorm s hs).trans hKC, ?_, ?_⟩
  · intro i
    have HM := (HP s hs).2.1 i
    have heq : Real.exp (exitClockLogMultiplier I i Y s) = exitTailMultiplier β i s := rfl
    have Hval : exitClockFlow I (Y, s) i.succ = Y i.succ * Real.exp (exitClockLogMultiplier I i Y s) := by
      rw [heq]
      simpa only [hβ0] using HM.1
    refine ⟨Hval, (HL i).1, ?_, ?_, ?_⟩
    · rw [heq]
      apply le_trans _ HM.2.1
      apply (div_le_div_iff₀ hC0 hA0).mpr
      nlinarith only [hAC, hC0]
    · rw [heq]
      exact HM.2.2.trans (by linarith only [hAC, hA0])
    · exact exitClockFlow_wall_differential hIo hI hUo hYU HR hT hcover (hclock ▸ hs) i
  · nlinarith only [(HL 0).2, (HL 1).2, mul_le_mul_of_nonneg_right hDC hs.1]
