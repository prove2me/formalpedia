-- Prove2me | solution 1 for BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T10:43:41.077382+00:00
-- url     : https://prove2.me/submissions/5eb40c65-6093-4bdc-aabb-9c5e1c03b3fc

import Definitions.Def_ChapterSoftmaxOrder
import Mathlib
import Definitions.Def_ChapterAttentionRetrieval
import Definitions.Def_ChapterSoftmaxBorn
import Definitions.Def_ChapterSoftmaxSharpness
-- Generated from ChapterAttentionRetrieval.lean — theorem BookProof.ChapterAttentionRetrieval.bornWeight_ge_of_dist_margin
open BookProof.ChapterSoftmaxBorn
open BookProof.ChapterSoftmaxSharpness
open BookProof.ChapterAttentionRetrieval


open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness BookProof.ChapterSoftmaxOrder

variable {m n : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
theorem solution {delta : ℝ} (q : EuclideanSpace ℝ (Fin n))
    (k : Fin m → EuclideanSpace ℝ (Fin n)) (j : Fin m)
    (hmargin : ∀ l, l ≠ j → ‖q - k j‖ ^ 2 + delta ≤ ‖q - k l‖ ^ 2) :
    1 - ((m : ℝ) - 1) * Real.exp (-delta) ≤ bornWeight q k j := by
  have hnum : ∀ l, bornNumer q (k l) = Real.exp (-‖q - k l‖ ^ 2) := by
    intro l
    unfold bornNumer BookProof.ChapterCoherentOverlap.coherentOverlap
    rw [← Real.exp_nat_mul, norm_sub_sq_real]
    congr 1; push_cast; ring
  set d : Fin m → ℝ := fun l => ‖q - k l‖ ^ 2 with hd
  have hS : ∑ l, bornNumer q (k l) ≤ Real.exp (-d j) * (1 + ((m : ℝ) - 1) * Real.exp (-delta)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    have hrest : ∑ l ∈ Finset.univ.erase j, bornNumer q (k l) ≤
        ∑ l ∈ Finset.univ.erase j, Real.exp (-d j) * Real.exp (-delta) := by
      refine Finset.sum_le_sum fun l hl => ?_
      rw [hnum, ← Real.exp_add]
      apply Real.exp_le_exp.2
      have := hmargin l (Finset.ne_of_mem_erase hl)
      simp only [hd]; linarith
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul] at hrest
    have hm1 : ((m - 1 : ℕ) : ℝ) = (m : ℝ) - 1 := by
      have : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact j.elim0)
      push_cast [this]; ring
    rw [hm1] at hrest
    rw [hnum j]
    nlinarith [Real.exp_pos (-d j)]
  have hpos : 0 < ∑ l, bornNumer q (k l) :=
    Finset.sum_pos (fun l _ => by rw [hnum]; exact Real.exp_pos _) ⟨j, Finset.mem_univ _⟩
  unfold bornWeight
  rw [hnum j, le_div_iff₀ hpos]
  set x := ((m : ℝ) - 1) * Real.exp (-delta)
  have hx : 0 ≤ x := by
    have : 1 ≤ m := Nat.one_le_iff_ne_zero.2 (fun h => by subst h; exact j.elim0)
    have : (1 : ℝ) ≤ m := by exact_mod_cast this
    exact mul_nonneg (by linarith) (Real.exp_pos _).le
  rcases le_or_gt (1 - x) 0 with h | h
  · have := mul_nonpos_of_nonpos_of_nonneg h hpos.le
    linarith [Real.exp_pos (-d j)]
  · calc (1 - x) * ∑ l, bornNumer q (k l) ≤ (1 - x) * (Real.exp (-d j) * (1 + x)) :=
          mul_le_mul_of_nonneg_left hS h.le
      _ = Real.exp (-d j) * (1 - x ^ 2) := by ring
      _ ≤ Real.exp (-d j) := by nlinarith [Real.exp_pos (-d j), sq_nonneg x]
