-- Prove2me | solution 1 for DetANN.Supplement.Thm32.dedup_set_spec
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-21T03:40:50.949661+00:00
-- url     : https://prove2.me/submissions/e0e870e5-829c-4109-90c7-2a65b5ac945c

import Mathlib
import Definitions.Def_DetANN_HPIMBSP
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_Exec
import Definitions.Def_DetANN_DataStructure
import Definitions.Def_DetANN_HPIMLayout
import Definitions.Def_DetANN_HPIMWF
import Definitions.Def_PNormRegLib_Reloc
import Definitions.Def_DetANN_HPIMPreBlocks
import Definitions.Def_DetANN_HPIMBalProg
import Definitions.Def_DetANN_Supplement_EvProg
import Definitions.Def_DetANN_Supplement_PreProg
import Definitions.Def_DetANN_Sylvester
import Definitions.Def_DetANN_Supplement_PreDedup
import Definitions.Def_DetANN_SignedBlocks


-- ===== T32_DedupMath =====
namespace DetANN.Supplement.Thm32

variable {d : ℕ}

lemma ddStep_mem {l : List (EuclideanSpace ℝ (Fin d))} {v w : EuclideanSpace ℝ (Fin d)} :
    w ∈ ddStep l v ↔ w ∈ l ∨ w = v := by
  unfold ddStep
  split_ifs with h
  · constructor
    · intro hw; exact Or.inl hw
    · rintro (hw | rfl); exact hw; exact h
  · simp [List.mem_append]

lemma ddStep_nodup {l : List (EuclideanSpace ℝ (Fin d))} (hl : l.Nodup) (v : EuclideanSpace ℝ (Fin d)) :
    (ddStep l v).Nodup := by
  unfold ddStep
  split_ifs with h
  · exact hl
  · exact List.nodup_append.2 ⟨hl, List.nodup_singleton v, by
      intro a ha b hb; simp at hb; subst hb; intro e; subst e; exact h ha⟩

lemma ddJ_mem (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)),
      w ∈ ddJ x i j kk l ↔ w ∈ l ∨ ∃ j', j ≤ j' ∧ j' < j + kk ∧ w = x i - x j' := by
  intro kk
  induction kk with
  | zero => intro j l w; simp only [ddJ]; constructor; exact Or.inl; rintro (h | ⟨_, h1, h2, _⟩); exact h; omega
  | succ kk ih =>
    intro j l w
    simp only [ddJ]
    rw [ih, ddStep_mem]
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

lemma ddI_mem (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))) (w : EuclideanSpace ℝ (Fin d)),
      w ∈ ddI x n i kk l ↔
        w ∈ l ∨ ∃ i' j', i ≤ i' ∧ i' < i + kk ∧ i' < j' ∧ j' < n ∧ w = x i' - x j' := by
  intro kk
  induction kk with
  | zero =>
    intro i l w; simp only [ddI]
    constructor; exact Or.inl; rintro (h | ⟨_, _, h1, h2, _⟩); exact h; omega
  | succ kk ih =>
    intro i l w
    simp only [ddI]
    rw [ih, ddJ_mem]
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

lemma ddJ_nodup (x : ℕ → EuclideanSpace ℝ (Fin d)) (i : ℕ) :
    ∀ (kk j : ℕ) (l : List (EuclideanSpace ℝ (Fin d))), l.Nodup → (ddJ x i j kk l).Nodup := by
  intro kk
  induction kk with
  | zero => intro j l h; exact h
  | succ kk ih => intro j l h; exact ih _ _ (ddStep_nodup h _)

lemma ddI_nodup (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) :
    ∀ (kk i : ℕ) (l : List (EuclideanSpace ℝ (Fin d))), l.Nodup → (ddI x n i kk l).Nodup := by
  intro kk
  induction kk with
  | zero => intro i l h; exact h
  | succ kk ih => intro i l h; exact ih _ _ (ddJ_nodup x i _ _ _ h)

lemma ddList_nodup (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) : (ddList x n).Nodup :=
  ddI_nodup x n n 0 [] List.nodup_nil

lemma ddList_mem (x : ℕ → EuclideanSpace ℝ (Fin d)) (n : ℕ) (w : EuclideanSpace ℝ (Fin d)) :
    w ∈ ddList x n ↔ ∃ i j, i < j ∧ j < n ∧ w = x i - x j := by
  unfold ddList
  rw [ddI_mem]
  constructor
  · rintro (h | ⟨i, j, _, _, h3, h4, h5⟩)
    · simp at h
    · exact ⟨i, j, h3, h4, h5⟩
  · rintro ⟨i, j, h3, h4, h5⟩; exact Or.inr ⟨i, j, by omega, by omega, h3, h4, h5⟩

/-- **The dedupe table as the set `𝒟` of `theorem_3_2_greedy`.** For injective `P`, the finset of the
table has no zero vector, contains `x - y` or `y - x` for all distinct points `x, y`, has as many
elements as the table has entries, and is nonempty when `n ≥ 2`. -/
theorem ddList_props {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin d)) (hP : Function.Injective P) :
    (∀ v ∈ (ddList (ptSeq P) n).toFinset, v ≠ 0) ∧
    (∀ y ∈ Finset.univ.image P, ∀ z ∈ Finset.univ.image P, y ≠ z →
      y - z ∈ (ddList (ptSeq P) n).toFinset ∨ z - y ∈ (ddList (ptSeq P) n).toFinset) ∧
    (ddList (ptSeq P) n).toFinset.card = (ddList (ptSeq P) n).length ∧
    (2 ≤ n → 1 ≤ (ddList (ptSeq P) n).toFinset.card) := by
  have hmem := ddList_mem (ptSeq P) n
  have pt : ∀ i (h : i < n), ptSeq P i = P ⟨i, h⟩ := fun i h => by simp [ptSeq, h]
  refine ⟨?_, ?_, List.toFinset_card_of_nodup (ddList_nodup _ n), ?_⟩
  · intro v hv
    rw [List.mem_toFinset, hmem] at hv
    obtain ⟨i, j, hij, hj, rfl⟩ := hv
    rw [pt i (by omega), pt j hj, sub_ne_zero]
    intro e; have := hP e; simp [Fin.ext_iff] at this; omega
  · intro y hy z hz hyz
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hy hz
    obtain ⟨a, rfl⟩ := hy; obtain ⟨b, rfl⟩ := hz
    simp only [List.mem_toFinset, hmem]
    have hab : (a : ℕ) ≠ b := fun e => hyz (by rw [Fin.ext e])
    rcases Nat.lt_or_gt_of_ne hab with h | h
    · left; exact ⟨a, b, h, b.isLt, by rw [pt a a.isLt, pt b b.isLt]⟩
    · right; exact ⟨b, a, h, a.isLt, by rw [pt a a.isLt, pt b b.isLt]⟩
  · intro hn
    apply Finset.card_pos.2
    refine ⟨ptSeq P 0 - ptSeq P 1, ?_⟩
    rw [List.mem_toFinset, hmem]
    exact ⟨0, 1, by omega, by omega, rfl⟩

end DetANN.Supplement.Thm32

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN

theorem _root_.solution :
    ∀ {d : ℕ} {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin d)) (hP : Function.Injective P),
    (∀ v ∈ (ddList (ptSeq P) n).toFinset, v ≠ 0) ∧
    (∀ y ∈ Finset.univ.image P, ∀ z ∈ Finset.univ.image P, y ≠ z →
      y - z ∈ (ddList (ptSeq P) n).toFinset ∨ z - y ∈ (ddList (ptSeq P) n).toFinset) ∧
    (ddList (ptSeq P) n).toFinset.card = (ddList (ptSeq P) n).length ∧
    (2 ≤ n → 1 ≤ (ddList (ptSeq P) n).toFinset.card) :=
  DetANN.Supplement.Thm32.ddList_props

end DetANN.Supplement.Thm32
