-- Prove2me | solution 1 for BianchiIX.exists_terminal_exitReturn_two_bounds_uniform
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T23:22:53.338131+00:00
-- url     : https://prove2.me/submissions/c7369f82-2c09-4bb0-be4f-34b8ac2b402a

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
import Theorems.Thm_BianchiIX_contDiffAt_normalizedMaxCurve_nat
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Theorems.Thm_BianchiIX_coreTailValid_of_height_le
import Theorems.Thm_BianchiIX_coreTail_regular_of_valid
import Theorems.Thm_BianchiIX_exists_exitClockFlow_second_variation
import Theorems.Thm_BianchiIX_exists_exitTail_second_variation_bound
import Theorems.Thm_BianchiIX_exists_exitTail_uniform_variation_budget
import Theorems.Thm_BianchiIX_exists_scalar_event_branch_two
import Theorems.Thm_BianchiIX_exists_terminal_exitClock_family
import Theorems.Thm_BianchiIX_exitTailField_jacobian_norm_bound
import Theorems.Thm_BianchiIX_exitTail_boundary_rate_small
import Theorems.Thm_BianchiIX_exitTail_perturbation_bounds
import Theorems.Thm_BianchiIX_fromProjectiveState_constraint
import Theorems.Thm_BianchiIX_hasDerivAt_projectiveOriginalFlow
import Theorems.Thm_BianchiIX_integral_exp_decay
import Theorems.Thm_BianchiIX_norm_slope_right_le_of_signedRowSum
import Theorems.Thm_BianchiIX_normalized_constraint_constant
import Theorems.Thm_BianchiIX_projective_inverse_scale
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
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
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
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic.Positivity
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
open Set

private theorem BianchiIX.exists_exitTail_uniform_second_bound {η : ℝ} (hη : 0 < η ∧ η ≤ 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ (α b T : ℝ) (Y X Z Q : ℝ → ExitTailState),
      (0 < α ∧ α ≤ 1) → 0 < b → b ≤ ε * α ^ J →
      (0 ≤ T ∧ T ≤ exitTailLength η α J) → Y 0 0 = 2 + 2 * α →
      |Y 0 1| + |Y 0 2| ≤ b →
      (∀ s ∈ Icc 0 T, HasDerivAt Y (exitTailField (Real.exp (-s)) (Y s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt X
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt Z
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (Z s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt Q
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (Q s) +
          fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (Y s) (X s) (Z s)) s) →
      Q 0 = 0 → ‖Q T‖ ≤ C * T * ‖X 0‖ * ‖Z 0‖ := by
  obtain ⟨A, hA, B, hB, ε, hε, H⟩ := exists_exitTail_uniform_variation_budget hη hJ
  obtain ⟨C, hC, HC⟩ := exists_exitTail_second_variation_bound
  have hC0 : 0 ≤ C := by linarith only [hC]
  have he : 1 ≤ Real.exp (9 * B) := Real.one_le_exp_iff.mpr (by positivity)
  refine ⟨C * Real.exp (9 * B), ?_, ε, hε, ?_⟩
  · nlinarith only [hC, he, mul_le_mul_of_nonneg_left he hC0]
  intro α b T Y X Z Q hα hb hsmall hT hR hw hY hX hZ hQ hQ0
  obtain ⟨hreg, hbudget⟩ := H α b T Y hα hb hsmall hT hR hw hY
  apply (HC Y X Z Q T α b A (80 * A) hT.1 hα.1.le hb.le (by linarith only [hA])
    (HasDerivAt.continuousOn hY) hreg hX hZ hQ hQ0).trans
  have he' := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget (by norm_num : (0 : ℝ) ≤ 9))
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he' hC0) hT.1) (norm_nonneg _))
    (norm_nonneg _)

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


/-- The ordinary first and second tail derivatives are uniform over an entire height interval. -/
theorem solution {η₀ : ℝ} (hη₀ : 0 < η₀ ∧ η₀ < 1)
    {J : ℕ} (hJ : 1 ≤ J) :
    ∃ C ≥ (1 : ℝ), ∃ ε > (0 : ℝ), ∀ η α b u w : ℝ,
      η₀ ≤ η → η < 1 → (0 < α ∧ α ≤ 1) → 0 < b →
      b ≤ ε * α ^ J → |u| + |w| ≤ b →
      let Y : ExitTailState := ![2 + 2 * α, u, w]
      let h := η * α ^ J
      coreTailValid h Y ∧ ContDiffAt ℝ 2 (fun Z => toExitTailState (coreTailState h Z)) Y ∧
        ‖fderiv ℝ (fun Z => toExitTailState (coreTailState h Z)) Y‖ ≤ C ∧
        ‖fderiv ℝ (fderiv ℝ (fun Z => toExitTailState (coreTailState h Z))) Y‖ ≤
          C * exitTailLength η α J := by
  obtain ⟨εe, hεe, HE⟩ := exists_terminal_exitClock_family hη₀ hJ
  obtain ⟨C₁, hC₁, ε₁, hε₁, H₁⟩ := exists_exitTail_uniform_linear_bound ⟨hη₀.1, hη₀.2.le⟩ hJ
  obtain ⟨C₂, hC₂, ε₂, hε₂, H₂⟩ := exists_exitTail_uniform_second_bound ⟨hη₀.1, hη₀.2.le⟩ hJ
  let C := C₁ + C₂
  have hC : 1 ≤ C := by dsimp only [C]; linarith only [hC₁, hC₂]
  have hC0 : 0 ≤ C := le_trans (by norm_num) hC
  have hC₁' : C₁ ≤ C := by dsimp only [C]; linarith only [hC₂]
  have hC₂' : C₂ ≤ C := by dsimp only [C]; linarith only [hC₁]
  let ε := min εe (min ε₁ ε₂)
  refine ⟨C, hC, ε, lt_min hεe (lt_min hε₁ hε₂), ?_⟩
  intro η α b u w hηlo hηhi hα hb hsmall hw Y h
  have hη : 0 < η := hη₀.1.trans_le hηlo
  have he : b ≤ εe * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right (min_le_left _ _) (pow_nonneg hα.1.le J))
  have hsmall₁ : b ≤ ε₁ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_left _ _)) (pow_nonneg hα.1.le J))
  have hsmall₂ : b ≤ ε₂ * α ^ J := hsmall.trans
    (mul_le_mul_of_nonneg_right ((min_le_right _ _).trans (min_le_right _ _)) (pow_nonneg hα.1.le J))
  obtain ⟨HV₀, I, hIo, hI, hcover, U, hUo, hYU, HR, hinit, _, HF⟩ := HE α b u w hα hb he hw
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
  have hend := coreTailState_eventuallyEq_exitClockFlow hIo hI hUo hYU HR HV
    (hcover ⟨HV.1.1.1.le, htime⟩)
  rw [heh] at hend
  let β : ℝ → ExitTailState := fun s => exitClockFlow I (Y, s)
  have hβ0 : β 0 = Y := hinit
  have hR : β 0 0 = 2 + 2 * α := by rw [hβ0]; rfl
  have hwall : |β 0 1| + |β 0 2| ≤ b := by rw [hβ0]; exact hw
  have hβ (s : ℝ) (hs : s ∈ Icc 0 S₀) : HasDerivAt β (exitTailField (Real.exp (-s)) (β s)) s :=
    (HF s hs).2.1
  have hvar0 (v : ExitTailState) : fderiv ℝ (exitClockFlow I) (Y, 0) (v, 0) = v :=
    exitClockFlow_variation_initial hIo hI hUo hYU HR (hcover ⟨le_rfl, hT⟩) v
  have hΦ := (HF S hs).1
  have hslice : ContDiffAt ℝ 2 (fun Z => exitClockFlow I (Z, S)) Y :=
    ContDiffAt.comp (g := exitClockFlow I) (f := fun Z : ExitTailState => (Z, S)) Y
      hΦ (contDiffAt_id.prodMk (contDiffAt_const (c := S)))
  refine ⟨HV, hslice.congr_of_eventuallyEq hend, ?_, ?_⟩
  · rw [hend.fderiv_eq]
    apply ContinuousLinearMap.opNorm_le_bound _ hC0
    intro v
    rw [fderiv_parameterSlice_apply (hΦ.differentiableAt (by norm_num)) v]
    have HB := H₁ α b S₀ β hα hb hsmall₁ ⟨hS₀, le_rfl⟩ hR hwall hβ
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0)) 0 S le_rfl hS hSS₀
      (fun r hr => (HF r (hsub hr)).2.2 v)
    rw [hvar0] at HB
    exact HB.trans (mul_le_mul_of_nonneg_right hC₁' (norm_nonneg v))
  · rw [hend.fderiv.fderiv_eq]
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hC0 hS)
    intro v
    apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (mul_nonneg hC0 hS) (norm_nonneg v))
    intro w
    obtain ⟨Q, hQ0, HQ⟩ := exists_exitClockFlow_second_variation hIo hI hUo hYU HR hT hcover v w
    rw [hclock] at HQ
    rw [← (HQ S hs).1]
    have HB := H₂ α b S β
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (v, 0))
      (fun r => fderiv ℝ (exitClockFlow I) (Y, r) (w, 0)) Q
      hα hb hsmall₂ hs hR hwall (fun r hr => hβ r (hsub hr))
      (fun r hr => (HF r (hsub hr)).2.2 v) (fun r hr => (HF r (hsub hr)).2.2 w)
      (fun r hr => (HQ r (hsub hr)).2) hQ0
    rw [hvar0, hvar0] at HB
    exact HB.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hC₂' hS) (norm_nonneg v)) (norm_nonneg w))
