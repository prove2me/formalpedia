-- Prove2me | solution 1 for ExtraConsensus.Sublinear.eq_3_5
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:12:38.186138+00:00
-- url     : https://prove2.me/submissions/06bcad2a-d27e-4b5e-b9a3-765574323e6e

import Mathlib
import Definitions.Def_ExtraConsensus_Linear_Model

set_option autoImplicit false

namespace ECAux

open Matrix ExtraConsensus.Sublinear

variable {n p : ℕ}

lemma mix_add (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A + B) x = mix A x + mix B x := by
  funext i
  simp [mix, add_smul, Finset.sum_add_distrib]

lemma mix_sub (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A - B) x = mix A x - mix B x := by
  funext i
  simp [mix, sub_smul, Finset.sum_sub_distrib]

lemma mix_smulM (c : ℝ) (A : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (c • A) x = c • mix A x := by
  funext i
  simp [mix, mul_smul, Finset.smul_sum]

lemma mix_one (x : Stack n p) : mix (1 : Matrix (Fin n) (Fin n) ℝ) x = x := by
  funext i
  simp [mix, Matrix.one_apply, ite_smul]

lemma mix_mul (A B : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix (A * B) x = mix A (mix B x) := by
  funext i
  simp only [mix, Matrix.mul_apply, Finset.sum_smul, Finset.smul_sum, mul_smul]
  rw [Finset.sum_comm]

lemma mix_sub_r (A : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    mix A (x - y) = mix A x - mix A y := by
  funext i
  simp [mix, smul_sub, Finset.sum_sub_distrib]

lemma mix_add_r (A : Matrix (Fin n) (Fin n) ℝ) (x y : Stack n p) :
    mix A (x + y) = mix A x + mix A y := by
  funext i
  simp [mix, smul_add, Finset.sum_add_distrib]

lemma mix_zero_r (A : Matrix (Fin n) (Fin n) ℝ) : mix A (0 : Stack n p) = 0 := by
  funext i
  simp [mix]

lemma mix_sum {ι : Type*} (A : Matrix (Fin n) (Fin n) ℝ) (s : Finset ι) (f : ι → Stack n p) :
    mix A (∑ k ∈ s, f k) = ∑ k ∈ s, mix A (f k) := by
  funext i
  simp only [mix, Finset.sum_apply, Finset.smul_sum]
  rw [Finset.sum_comm]

lemma extraIter_rec (α : ℝ) (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (x0 : Stack n p) (k : ℕ) :
    extraIter α W Wt f x0 (k + 2) =
      mix (1 + W) (extraIter α W Wt f x0 (k + 1)) - mix Wt (extraIter α W Wt f x0 k)
        - α • (gradF f (extraIter α W Wt f x0 (k + 1)) - gradF f (extraIter α W Wt f x0 k)) := rfl

lemma eq35 (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (α : ℝ) (x0 : Stack n p) (k : ℕ) :
    extraIter α W Wt f x0 (k + 1) = mix Wt (extraIter α W Wt f x0 k)
      - ∑ t ∈ Finset.range (k + 1), mix (Wt - W) (extraIter α W Wt f x0 t)
      - α • gradF f (extraIter α W Wt f x0 k) := by
  induction k with
  | zero =>
    simp only [zero_add, Finset.range_one, Finset.sum_singleton]
    show mix W x0 - α • gradF f x0 = _
    rw [mix_sub]
    abel
  | succ k ih =>
    set x1 := extraIter α W Wt f x0 (k + 1) with hx1
    set xk := extraIter α W Wt f x0 k with hxk
    have hS : ∑ t ∈ Finset.range (k + 1), mix (Wt - W) (extraIter α W Wt f x0 t)
        = mix Wt xk - x1 - α • gradF f xk := by
      rw [ih]; abel
    rw [Finset.sum_range_succ, hS, extraIter_rec, mix_sub, mix_add, mix_one, smul_sub]
    abel

end ECAux

open Matrix ECAux in
theorem solution {n p : ℕ} (W Wt : Matrix (Fin n) (Fin n) ℝ)
    (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (α : ℝ) (x0 : ExtraConsensus.Sublinear.Stack n p) :
    let x := ExtraConsensus.Sublinear.extraIter α W Wt f x0
    ∀ k : ℕ, x (k + 1) = ExtraConsensus.Sublinear.mix Wt (x k) - ∑ t ∈ Finset.range (k + 1), ExtraConsensus.Sublinear.mix (Wt - W) (x t)
      - α • ExtraConsensus.Sublinear.gradF f (x k) := by
  intro x k
  exact eq35 W Wt f α x0 k
