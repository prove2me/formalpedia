-- Prove2me | solution 1 for DerandSq.lemma_4_3
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-11T18:04:45.449188+00:00
-- url     : https://prove2.me/submissions/18c32c08-e629-4e30-aaa7-b73cc2c8d0a3

import Mathlib
import Definitions.Def_DerandSq_permMat
import Definitions.Def_DerandSq_dsAdj
import Definitions.Def_DerandSq_dsWalk

section
set_option autoImplicit false

namespace DerandSq.Dev.L43

open Matrix in
theorem entry_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) (w v : Fin N) :
    (DerandSq.permMat σ * DerandSq.permMat τ) w v = if σ (τ v) = w then 1 else 0 := by
  classical
  simp only [Matrix.mul_apply, DerandSq.permMat, Matrix.of_apply]
  rw [Finset.sum_eq_single (τ v)]
  · simp
  · intro u _ hu
    have : τ v ≠ u := fun h => hu h.symm
    simp [this]
  · simp

theorem dsAdj_eq {N d : ℕ} (π : Fin d → Equiv.Perm (Fin N)) (H : SimpleGraph (Fin d))
    [DecidableRel H.Adj] :
    DerandSq.dsAdj π H = ∑ a : Fin d, ∑ b : Fin d,
      (if H.Adj a b then DerandSq.permMat (π b) * DerandSq.permMat (π a) else 0) := by
  classical
  ext w v
  simp only [DerandSq.dsAdj, Matrix.of_apply, Matrix.sum_apply]
  rw [Finset.card_filter, ← Finset.univ_product_univ, Finset.sum_product]
  push_cast
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  by_cases h : H.Adj a b
  · simp [h, entry_mul]
  · simp [h]

end DerandSq.Dev.L43

namespace DerandSq
open DerandSq.Dev.L43 in
theorem chk_lemma_4_3 {N d k : ℕ} (H : SimpleGraph (Fin d)) [DecidableRel H.Adj]
    (hH : H.IsRegularOfDegree k) (π : Fin d → Equiv.Perm (Fin N)) :
    dsWalk π H k = ((d : ℝ) * k)⁻¹ • ∑ i : Fin d, ∑ j : Fin d,
        (if i < j ∧ H.Adj i j then
          permMat (π i) * permMat (π j) + permMat (π j) * permMat (π i) else 0) ∧
      dsAdj π H = ∑ i : Fin d, ∑ j : Fin d,
        (if i < j ∧ H.Adj i j then
          permMat (π i) * permMat (π j) + permMat (π j) * permMat (π i) else 0) := by
  have key : dsAdj π H = ∑ i : Fin d, ∑ j : Fin d,
        (if i < j ∧ H.Adj i j then
          permMat (π i) * permMat (π j) + permMat (π j) * permMat (π i) else 0) := by
    rw [dsAdj_eq]
    -- split each ordered adjacent pair by a<b or b<a
    have h1 : ∀ a b : Fin d, (if H.Adj a b then permMat (π b) * permMat (π a) else 0) =
        (if a < b ∧ H.Adj a b then permMat (π b) * permMat (π a) else 0) +
        (if b < a ∧ H.Adj b a then permMat (π b) * permMat (π a) else 0) := by
      intro a b
      by_cases h : H.Adj a b
      · have hne : a ≠ b := h.ne
        rcases lt_or_gt_of_ne hne with hl | hl
        · simp [h, hl, h.symm, not_lt.mpr hl.le]
        · simp [h, hl, h.symm, not_lt.mpr hl.le]
      · have : ¬ H.Adj b a := fun h' => h h'.symm
        simp [h, this]
    simp_rw [h1, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun a b => if b < a ∧ H.Adj b a then permMat (π b) * permMat (π a) else 0)]
    simp_rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp [add_comm]
  refine ⟨?_, key⟩
  unfold dsWalk
  rw [key]
end DerandSq
end

theorem solution : type_of% @DerandSq.chk_lemma_4_3 := @DerandSq.chk_lemma_4_3
