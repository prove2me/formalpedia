-- Prove2me | solution 1 for BianchiIX.exists_exitTail_second_variation_bound
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T19:38:17.723147+00:00
-- url     : https://prove2.me/submissions/588c8d29-3f2c-4c76-a086-9e5223d213dc

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_TerminalConnectionData
import Definitions.Def_BianchiIX_TerminalConeData
import Theorems.Thm_BianchiIX_exists_exitTail_field_two_bounds
import Theorems.Thm_BianchiIX_exitTailField_jacobian_norm_bound
import Theorems.Thm_BianchiIX_exitTail_boundary_rate_small
import Theorems.Thm_BianchiIX_exitTail_perturbation_bounds
import Theorems.Thm_BianchiIX_integral_exp_decay
import Theorems.Thm_BianchiIX_norm_slope_right_le_of_signedRowSum
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Topology.Order.ProjIcc
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Topology.Order.Compact
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral

noncomputable section
open BianchiIX
open Set MeasureTheory

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
open Set

private theorem BianchiIX.exists_exitTail_hessian_forcing_bound :
    ∃ C ≥ (1 : ℝ), ∀ (v : ℝ) (Y ξ ζ : ExitTailState),
      (7 / 4 ≤ Y 0 ∧ Y 0 ≤ 17 / 4) → |Y 1| ≤ 1 / 100 →
      (0 ≤ v ∧ v ≤ 1) → |Y 2| ≤ 1 / 100 →
      ‖fderiv ℝ (fderiv ℝ (exitTailField v)) Y ξ ζ‖ ≤ C * ‖ξ‖ * ‖ζ‖ := by
  obtain ⟨C, hC, H⟩ := exists_exitTail_field_two_bounds
  refine ⟨C, hC, ?_⟩
  intro v Y ξ ζ hR hu hv hw
  have HB := (H v Y hR hu hv hw).2.2
  exact ((fderiv ℝ (fderiv ℝ (exitTailField v)) Y ξ).le_opNorm ζ).trans
    (mul_le_mul_of_nonneg_right
      (((fderiv ℝ (fderiv ℝ (exitTailField v)) Y).le_opNorm ξ).trans
        (mul_le_mul_of_nonneg_right HB (norm_nonneg ξ))) (norm_nonneg ζ))

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


/-- The bounded state Hessian and the integrated Jacobian give linear, rather than exponential, duration loss. -/
theorem solution :
    ∃ C ≥ (1 : ℝ), ∀ (Y X Z Q : ℝ → ExitTailState) (T α b A D : ℝ),
      0 ≤ T → 0 ≤ α → 0 ≤ b → 0 ≤ A →
      ContinuousOn Y (Icc 0 T) →
      (∀ s ∈ Icc 0 T, exitTailRegion α b A D (Y s)) →
      (∀ s ∈ Icc 0 T, HasDerivAt X
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (X s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt Z
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (Z s)) s) →
      (∀ s ∈ Icc 0 T, HasDerivAt Q
        (fderiv ℝ (exitTailField (Real.exp (-s))) (Y s) (Q s) +
          fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (Y s) (X s) (Z s)) s) →
      Q 0 = 0 →
      ‖Q T‖ ≤ C * Real.exp (9 * exitTailVariationBudget α b A D T) * T * ‖X 0‖ * ‖Z 0‖ := by
  obtain ⟨C, hC, HC⟩ := exists_exitTail_hessian_forcing_bound
  refine ⟨C, hC, ?_⟩
  intro Y X Z Q T α b A D hT hα hb hA hY hreg hX hZ hQ hQ0
  let B := exitTailVariationBudget α b A D T
  let L := Real.exp (3 * B)
  have hL : 0 ≤ L := (Real.exp_pos _).le
  have HX (s : ℝ) (hs : s ∈ Icc 0 T) : ‖X s‖ ≤ L * ‖X 0‖ :=
    exitTail_variation_bound hT hα hb hA hY hreg le_rfl hs.1 hs.2
      (fun r hr => hX r ⟨hr.1, hr.2.trans hs.2⟩)
  have HZ (s : ℝ) (hs : s ∈ Icc 0 T) : ‖Z s‖ ≤ L * ‖Z 0‖ :=
    exitTail_variation_bound hT hα hb hA hY hreg le_rfl hs.1 hs.2
      (fun r hr => hZ r ⟨hr.1, hr.2.trans hs.2⟩)
  have HP (s : ℝ) (hs : s ∈ Icc 0 T) :
      ‖fderiv ℝ (fderiv ℝ (exitTailField (Real.exp (-s)))) (Y s) (X s) (Z s)‖ ≤
        C * L ^ 2 * ‖X 0‖ * ‖Z 0‖ := by
    have hv : 0 ≤ Real.exp (-s) ∧ Real.exp (-s) ≤ 1 :=
      ⟨(Real.exp_pos _).le, Real.exp_le_one_iff.mpr (neg_nonpos.mpr hs.1)⟩
    have H := HC (Real.exp (-s)) (Y s) (X s) (Z s)
      (hreg s hs).1 (hreg s hs).2.1 hv (hreg s hs).2.2.1
    apply H.trans
    calc
      C * ‖X s‖ * ‖Z s‖ ≤ C * (L * ‖X 0‖) * (L * ‖Z 0‖) := by
        gcongr
        · exact HX s hs
        · exact HZ s hs
      _ = _ := by ring
  have H := exitTail_forced_variation_bound hT hα hb hA hY hreg le_rfl hT le_rfl hQ
    (R := fun _ => C * L ^ 2 * ‖X 0‖ * ‖Z 0‖) continuousOn_const HP
  simp only [hQ0, norm_zero, zero_add, intervalIntegral.integral_const, sub_zero,
    smul_eq_mul] at H
  apply H.trans_eq
  have hpow : L * L ^ 2 = Real.exp (9 * B) := by
    dsimp only [L]
    rw [sq, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  change L * (T * (C * L ^ 2 * ‖X 0‖ * ‖Z 0‖)) = _
  calc
    _ = C * (L * L ^ 2) * T * ‖X 0‖ * ‖Z 0‖ := by ring
    _ = _ := by rw [hpow]
