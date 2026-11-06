-- Prove2me | solution 1 for BianchiIX.norm_le_exp_of_signedRowSum
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:40:47.065078+00:00
-- url     : https://prove2.me/submissions/746dbe1d-5dfe-4cc4-a8e4-1ec18ceb6ad7

import Definitions.Def_BianchiIX_Analysis_SignedRowGrowth
import Theorems.Thm_BianchiIX_norm_le_initial_of_signedRowSum_nonpos
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Data.Matrix.Mul
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.FunProp

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

noncomputable section
open BianchiIX
open Set Filter
open scoped Topology
variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]


theorem solution {f : ℝ → (ι → ℝ)}
    {A : ℝ → Matrix ι ι ℝ} {z z' : ℝ → ℝ} {a b : ℝ}
    (hf : ContinuousOn f (Icc a b))
    (hderiv : ∀ t ∈ Ico a b, HasDerivAt f ((A t).mulVec (f t)) t)
    (hz : ContinuousOn z (Icc a b))
    (hzderiv : ∀ t ∈ Ico a b, HasDerivAt z (z' t) t)
    (hA : ∀ t ∈ Ico a b, ∀ i, signedRowSum (A t) i ≤ z' t) :
    ∀ t ∈ Icc a b, ‖f t‖ ≤ ‖f a‖ * Real.exp (z t - z a) := by
  let g : ℝ → (ι → ℝ) := fun t => Real.exp (-z t) • f t
  let B : ℝ → Matrix ι ι ℝ := fun t => A t - z' t • (1 : Matrix ι ι ℝ)
  have hg (t : ℝ) (ht : t ∈ Ico a b) : HasDerivAt g ((B t).mulVec (g t)) t := by
    convert! ((hzderiv t ht).neg.exp).smul (hderiv t ht) using 1
    dsimp [B, g]
    rw [Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    simp only [Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
    ring
  have hB (t : ℝ) (ht : t ∈ Ico a b) (i : ι) : signedRowSum (B t) i ≤ 0 := by
    dsimp [B]
    rw [signedRowSum_sub_scalar]
    exact sub_nonpos.mpr (hA t ht i)
  have H := norm_le_initial_of_signedRowSum_nonpos
    ((Real.continuous_exp.comp_continuousOn hz.neg).smul hf) hg hB
  intro t ht
  have hn (s : ℝ) : ‖g s‖ = Real.exp (-z s) * ‖f s‖ := by
    simp only [g, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  have H' := H t ht
  change ‖g t‖ ≤ ‖g a‖ at H'
  rw [hn, hn] at H'
  calc
    ‖f t‖ = Real.exp (z t) * (Real.exp (-z t) * ‖f t‖) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp
    _ ≤ Real.exp (z t) * (Real.exp (-z a) * ‖f a‖) :=
      mul_le_mul_of_nonneg_left H' (Real.exp_pos _).le
    _ = ‖f a‖ * Real.exp (z t - z a) := by
      rw [← mul_assoc, ← Real.exp_add]
      simp only [sub_eq_add_neg, mul_comm]
