-- Prove2me | solution 1 for ExtraConsensus.Linear.lemma_3_2
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T09:12:35.244783+00:00
-- url     : https://prove2.me/submissions/116cf5c7-70fd-40e6-bd86-831146dea169

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


lemma proj_mix (A : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) (i : Fin n) (l : Fin p) :
    EuclideanSpace.proj l (mix A x i) = (A *ᵥ (fun j => EuclideanSpace.proj l (x j))) i := by
  simp [mix, Matrix.mulVec, dotProduct]

lemma mix_eq_zero_iff (A : Matrix (Fin n) (Fin n) ℝ) (x : Stack n p) :
    mix A x = 0 ↔ ∀ l : Fin p, A *ᵥ (fun j => EuclideanSpace.proj l (x j)) = 0 := by
  constructor
  · intro h l
    funext i
    rw [← proj_mix, h]
    simp
  · intro h
    funext i
    ext l
    have := congrFun (h l) i
    rw [← proj_mix] at this
    simpa using this

end ECAux

open Matrix ECAux ExtraConsensus.Sublinear in
theorem solution {n p : ℕ} (hn : 0 < n) (Gr : SimpleGraph (Fin n))
    (W Wt U : Matrix (Fin n) (Fin n) ℝ) (f : Fin n → EuclideanSpace ℝ (Fin p) → ℝ) (Lf α : ℝ)
    (hA1 : ExtraConsensus.Linear.MixingAssumption Gr W Wt) (hA2 : ExtraConsensus.Sublinear.ConvexLipschitzGrad f Lf) (hA3 : ExtraConsensus.Sublinear.SolutionExists f)
    (hUs : Uᵀ = U) (hUpsd : U.PosSemidef) (hU2 : U * U = Wt - W)
    (qs xs : ExtraConsensus.Sublinear.Stack n p) (hopt : ExtraConsensus.Sublinear.IsOptimalPair U α f qs xs) (x0 : ExtraConsensus.Sublinear.Stack n p) :
    let x := ExtraConsensus.Sublinear.extraIter α W Wt f x0
    let q := ExtraConsensus.Sublinear.qSeq U x
    ∀ k : ℕ, ExtraConsensus.Sublinear.mix (1 + W - (2 : ℝ) • Wt) (x (k + 1) - xs) + ExtraConsensus.Sublinear.mix Wt (x (k + 1) - x k)
      = -(ExtraConsensus.Sublinear.mix U (q (k + 1) - qs)) - α • (ExtraConsensus.Sublinear.gradF f (x k) - ExtraConsensus.Sublinear.gradF f xs) := by
  intro x q k
  have hx : x = extraIter α W Wt f x0 := rfl
  have hq : q = qSeq U x := rfl
  clear_value q x
  obtain ⟨-, hopt1, hopt2⟩ := hopt
  -- (Wt - W) xs = 0 and (1 - Wt) xs = 0
  have hWtW : mix (Wt - W) xs = 0 := by
    rw [← hU2, mix_mul, hopt2, mix_zero_r]
  have h1Wt : mix (1 - Wt) xs = 0 := by
    rw [mix_eq_zero_iff]
    intro l
    have hl := (mix_eq_zero_iff U xs).1 hopt2 l
    have hl2 : (W - Wt) *ᵥ (fun j => EuclideanSpace.proj l (xs j)) = 0 := by
      have : W - Wt = -(U * U) := by rw [hU2]; abel
      rw [this, Matrix.neg_mulVec, ← Matrix.mulVec_mulVec, hl, Matrix.mulVec_zero, neg_zero]
    obtain ⟨c, hc⟩ := (hA1.null_W_sub_Wt _).1 hl2
    rw [hc]
    have : (fun _ : Fin n => c) = c • (fun _ : Fin n => (1 : ℝ)) := by
      funext j; simp
    rw [this, Matrix.mulVec_smul, hA1.null_one_sub_Wt, smul_zero]
  have hcomb : mix (1 + W - (2 : ℝ) • Wt) xs = 0 := by
    have : (1 + W - (2 : ℝ) • Wt) = (1 - Wt) - (Wt - W) := by
      rw [two_smul]; abel
    rw [this, mix_sub, h1Wt, hWtW, sub_zero]
  -- facts about the iteration
  have h35 : ∀ k, x (k + 1) = mix Wt (x k) - ∑ t ∈ Finset.range (k + 1), mix (Wt - W) (x t)
      - α • gradF f (x k) := by
    intro k; rw [hx]; exact eq35 W Wt f α x0 k
  have hrec : ∀ k, x (k + 2) = mix (1 + W) (x (k + 1)) - mix Wt (x k)
      - α • (gradF f (x (k + 1)) - gradF f (x k)) := by
    intro k; rw [hx]; exact extraIter_rec α W Wt f x0 k
  have hqU : mix U (q (k + 1)) = ∑ t ∈ Finset.range (k + 2), mix (Wt - W) (x t) := by
    rw [hq]
    unfold qSeq
    rw [mix_sum]
    refine Finset.sum_congr rfl (fun t _ => ?_)
    rw [← mix_mul, hU2]
  have e2 : x (k + 2) = mix Wt (x (k + 1)) - ∑ t ∈ Finset.range (k + 2), mix (Wt - W) (x t)
      - α • gradF f (x (k + 1)) := h35 (k + 1)
  have e3 := hrec k
  have hS2 : ∑ t ∈ Finset.range (k + 2), mix (Wt - W) (x t)
      = mix Wt (x (k + 1)) - x (k + 2) - α • gradF f (x (k + 1)) := by
    rw [e2]; abel
  have hM : mix (1 + W - (2 : ℝ) • Wt) (x (k + 1)) =
      x (k + 1) + mix W (x (k + 1)) - (2 : ℝ) • mix Wt (x (k + 1)) := by
    rw [mix_sub, mix_add, mix_one, mix_smulM]
  have e3' : x (k + 2) = x (k + 1) + mix W (x (k + 1)) - mix Wt (x k)
      - α • (gradF f (x (k + 1)) - gradF f (x k)) := by
    rw [e3, mix_add, mix_one]
  rw [mix_sub_r (1 + W - (2 : ℝ) • Wt) (x (k + 1)) xs, mix_sub_r Wt (x (k + 1)) (x k),
    mix_sub_r U (q (k + 1)) qs]
  linear_combination (norm := module) hM - hcomb + hqU + hS2 - e3' - hopt1
