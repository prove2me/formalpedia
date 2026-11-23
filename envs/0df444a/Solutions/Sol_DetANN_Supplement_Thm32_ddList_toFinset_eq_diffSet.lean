-- Prove2me | solution 1 for DetANN.Supplement.Thm32.ddList_toFinset_eq_diffSet
-- status  : ACCEPTED   (prove)
-- author  : @Mr Robbins
-- created : 2026-11-23T02:53:12.558011+00:00
-- url     : https://prove2.me/submissions/3d157312-7818-4410-bb12-8cd51e504129

import Mathlib
import Definitions.Def_DetANN_Construction
import Definitions.Def_DetANN_Supplement_PreDedup

open DetANN
open DetANN.Supplement.Thm32

namespace DetANN.Supplement.Thm32

variable {d : ℕ}

lemma ddStep_mem' {l : List (EuclideanSpace ℝ (Fin d))} {v w : EuclideanSpace ℝ (Fin d)} :
    w ∈ ddStep l v ↔ w ∈ l ∨ w = v := by
  unfold ddStep
  split_ifs with h
  · constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | rfl); exact hw; exact h
  · simp [List.mem_append]

lemma ddJ_mem' (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)),
      w ∈ ddJ x i j kk l ↔ w ∈ l ∨ ∃ j', j ≤ j' ∧ j' < j + kk ∧ w = x i - x j' := by
  intro kk
  induction kk with
  | zero =>
      intro j l w
      simp only [ddJ]
      constructor
      · exact Or.inl
      · rintro (h | ⟨_, h1, h2, _⟩)
        · exact h
        · omega
  | succ kk ih =>
      intro j l w
      simp only [ddJ]
      rw [ih, ddStep_mem']
      constructor
      · rintro ((h | h) | ⟨j', h1, h2, h3⟩)
        · exact Or.inl h
        · exact Or.inr ⟨j, le_rfl, by omega, h⟩
        · exact Or.inr ⟨j', by omega, by omega, h3⟩
      · rintro (h | ⟨j', h1, h2, h3⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.eq_or_lt_of_le h1 with e | e
          · subst e; exact Or.inl (Or.inr h3)
          · exact Or.inr ⟨j', by omega, by omega, h3⟩

lemma ddI_mem' (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)),
      w ∈ ddI x n i kk l ↔
        w ∈ l ∨ ∃ i' j', i ≤ i' ∧ i' < i + kk ∧ i' < j' ∧ j' < n ∧ w = x i' - x j' := by
  intro kk
  induction kk with
  | zero =>
      intro i l w
      simp only [ddI]
      constructor
      · exact Or.inl
      · rintro (h | ⟨_, _, h1, h2, _⟩)
        · exact h
        · omega
  | succ kk ih =>
      intro i l w
      simp only [ddI]
      rw [ih, ddJ_mem']
      constructor
      · rintro ((h | ⟨j', h1, h2, h3⟩) | ⟨i', j', h1, h2, h3, h4, h5⟩)
        · exact Or.inl h
        · exact Or.inr ⟨i, j', le_rfl, by omega, by omega, by omega, h3⟩
        · exact Or.inr ⟨i', j', by omega, by omega, h3, h4, h5⟩
      · rintro (h | ⟨i', j', h1, h2, h3, h4, h5⟩)
        · exact Or.inl (Or.inl h)
        · rcases Nat.eq_or_lt_of_le h1 with e | e
          · subst e; exact Or.inl (Or.inr ⟨j', by omega, by omega, h5⟩)
          · exact Or.inr ⟨i', j', by omega, by omega, h3, h4, h5⟩

lemma ddList_mem' (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) (w : EuclideanSpace ℝ (Fin d)) :
    w ∈ ddList x n ↔ ∃ i j, i < j ∧ j < n ∧ w = x i - x j := by
  unfold ddList
  rw [ddI_mem']
  constructor
  · rintro (h | ⟨i, j, _, _, h3, h4, h5⟩)
    · simp at h
    · exact ⟨i, j, h3, h4, h5⟩
  · rintro ⟨i, j, h3, h4, h5⟩
    exact Or.inr ⟨i, j, by omega, by omega, h3, h4, h5⟩

lemma ddStep_nodup' {l : List (EuclideanSpace ℝ (Fin d))} (hl : l.Nodup)
    (v : EuclideanSpace ℝ (Fin d)) : (ddStep l v).Nodup := by
  unfold ddStep
  split_ifs with h
  · exact hl
  · exact List.nodup_append.2 ⟨hl, List.nodup_singleton v, by
      intro a ha b hb
      simp at hb
      subst hb
      intro e
      subst e
      exact h ha⟩

lemma ddJ_nodup' (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))), l.Nodup → (ddJ x i j kk l).Nodup := by
  intro kk
  induction kk with
  | zero => intro j l h; exact h
  | succ kk ih => intro j l h; exact ih _ _ (ddStep_nodup' h _)

lemma ddI_nodup' (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))), l.Nodup → (ddI x n i kk l).Nodup := by
  intro kk
  induction kk with
  | zero => intro i l h; exact h
  | succ kk ih => intro j l h; exact ih _ _ (ddJ_nodup' x j _ _ _ h)

lemma ddList_nodup' (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : (ddList x n).Nodup :=
  ddI_nodup' x n n 0 [] List.nodup_nil

end DetANN.Supplement.Thm32

/-- The deduplicated loop table is exactly the padded difference finset, and its length is the
cardinality of that finset. -/
theorem solution {d n : ℕ} (k : ℕ)
    (P : Fin n → EuclideanSpace ℝ (Fin d)) :
    (ddList (ptSeq (fun i => padVec (2 ^ k) (P i))) n).toFinset = diffSet k P ∧
      (ddList (ptSeq (fun i => padVec (2 ^ k) (P i))) n).length = (diffSet k P).card := by
  have hset : (ddList (ptSeq (fun i => padVec (2 ^ k) (P i))) n).toFinset = diffSet k P := by
    ext w
    rw [List.mem_toFinset, ddList_mem']
    constructor
    · rintro ⟨i, j, hij, hjn, rfl⟩
      have hin : i < n := by omega
      simp only [diffSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      refine ⟨(⟨i, hin⟩, ⟨j, hjn⟩), hij, ?_⟩
      simp [ptSeq, hin, hjn]
    · simp only [diffSet, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
      rintro ⟨⟨i, j⟩, hij, rfl⟩
      exact ⟨i, j, hij, j.isLt, by simp [ptSeq, i.isLt, j.isLt]⟩
  refine ⟨hset, ?_⟩
  rw [← List.toFinset_card_of_nodup (ddList_nodup' _ n), hset]
