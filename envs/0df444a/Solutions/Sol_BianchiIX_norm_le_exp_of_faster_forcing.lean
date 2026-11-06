-- Prove2me | solution 1 for BianchiIX.norm_le_exp_of_faster_forcing
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T15:11:07.186414+00:00
-- url     : https://prove2.me/submissions/7f4bd1f9-ab40-494d-8967-1cb0d8637781

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Theorems.Thm_BianchiIX_norm_slope_right_le_of_signedRowSum
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Prod

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

noncomputable section
open BianchiIX
open Set
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


theorem solution {f q : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {ρ Q T : ℝ} (hρ : 0 < ρ) (hQ : 0 ≤ Q)
    (hf : ∀ t ∈ Icc 0 T, HasDerivAt f ((A t).mulVec (f t) + q t) t)
    (hA : ∀ t ∈ Icc 0 T, ∀ i, signedRowSum (A t) i ≤ -ρ)
    (hq : ∀ t ∈ Icc 0 T, ‖q t‖ ≤ Q * Real.exp (-2 * ρ * t)) :
    ∀ t ∈ Icc 0 T, ‖f t‖ ≤ (‖f 0‖ + Q / ρ) * Real.exp (-ρ * t) := by
  let g := fun t => Real.exp (ρ * t) • f t
  let M := fun t => A t - (-ρ) • (1 : Matrix ι ι ℝ)
  let c := fun t => Real.exp (ρ * t) • q t
  let B := fun t => ‖f 0‖ + Q / ρ * (1 - Real.exp (-ρ * t))
  have hg (t : ℝ) (ht : t ∈ Icc 0 T) : HasDerivAt g ((M t).mulVec (g t) + c t) t := by
    convert! (((hasDerivAt_id t).const_mul ρ).exp).smul (hf t ht) using 1
    dsimp [M, g, c]
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hM (t : ℝ) (ht : t ∈ Ico 0 T) (i : ι) : signedRowSum (M t) i ≤ 0 := by
    dsimp [M]
    rw [signedRowSum_sub_scalar]
    linarith only [hA t (Ico_subset_Icc_self ht) i]
  have hB (t : ℝ) : HasDerivAt B (Q * Real.exp (-ρ * t)) t := by
    convert! (((hasDerivAt_const t (1 : ℝ)).sub
      (((hasDerivAt_id t).const_mul (-ρ)).exp)).const_mul (Q / ρ)).const_add ‖f 0‖ using 1
    dsimp
    field_simp
    ring
  have hc (t : ℝ) (ht : t ∈ Icc 0 T) : ‖c t‖ ≤ Q * Real.exp (-ρ * t) := by
    simp only [c, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    calc
      _ ≤ Real.exp (ρ * t) * (Q * Real.exp (-2 * ρ * t)) :=
        mul_le_mul_of_nonneg_left (hq t ht) (Real.exp_pos _).le
      _ = Q * (Real.exp (ρ * t) * Real.exp (-2 * ρ * t)) := by ring
      _ = Q * Real.exp (-ρ * t) := by rw [← Real.exp_add]; congr 2; ring
  have H := norm_le_of_forced_signedRowSum_nonpos (HasDerivAt.continuousOn hg)
    (fun t ht => hg t (Ico_subset_Icc_self ht)) hM
    (HasDerivAt.continuousOn (fun t _ => hB t)) (fun t _ => hB t)
    (by simp [g, B]) (fun t ht => hc t (Ico_subset_Icc_self ht))
  intro t ht
  have H' := H t ht
  simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at H'
  have hBt : B t ≤ ‖f 0‖ + Q / ρ := by
    dsimp [B]
    have hn : 0 ≤ Q / ρ := div_nonneg hQ hρ.le
    nlinarith [Real.exp_pos (-ρ * t)]
  calc
    ‖f t‖ = Real.exp (-ρ * t) * (Real.exp (ρ * t) * ‖f t‖) := by
      rw [← mul_assoc, ← Real.exp_add]
      have he : -ρ * t + ρ * t = 0 := by ring
      rw [he, Real.exp_zero, one_mul]
    _ ≤ Real.exp (-ρ * t) * (‖f 0‖ + Q / ρ) :=
      mul_le_mul_of_nonneg_left (H'.trans hBt) (Real.exp_pos _).le
    _ = _ := by ring
