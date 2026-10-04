-- Prove2me | solution 1 for BealeConvexMin.QuadSimplex.free_count_decreases
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T00:16:04.504978+00:00
-- url     : https://prove2.me/submissions/8bd1571e-2661-460b-93f4-439bcd1eba49

import Mathlib
import Definitions.Def_BealeConvexMin_QuadSimplex_pivotC
import Definitions.Def_BealeConvexMin_QuadSimplex_Tableau
import Definitions.Def_BealeConvexMin_QuadSimplex_BealeStep

set_option autoImplicit false

namespace BealeFreeCountAux

open BealeConvexMin.QuadSimplex

/-- A nonbasic free slot whose row of `c` vanishes off the diagonal. -/
def Clean {n N : ℕ} (T : Tableau n N) (k : Fin N) : Prop :=
  T.lab k = none ∧ ∀ l, l ≠ k.succ → T.c k.succ l = 0

theorem orient_lab {n N : ℕ} (T : Tableau n N) (p : Fin N) : (orient T p).lab = T.lab := by
  unfold orient; split_ifs <;> rfl

theorem orient_symm {n N : ℕ} (T : Tableau n N) (p : Fin N) (h : T.c.IsSymm) :
    (orient T p).c.IsSymm := by
  unfold orient
  split_ifs
  · apply Matrix.IsSymm.ext
    intro i j
    simp only [negateSlot, Matrix.of_apply]
    rw [h.apply i j]
    ring
  · exact h

theorem orient_clean {n N : ℕ} (T : Tableau n N) (p k : Fin N) (h : Clean T k) :
    Clean (orient T p) k := by
  unfold orient
  split_ifs
  · refine ⟨h.1, fun l hl => ?_⟩
    simp only [negateSlot, Matrix.of_apply]
    rw [h.2 l hl]; ring
  · exact h

theorem pivotC_symm {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (P : Fin (N + 1))
    (d : Fin (N + 1) → ℝ) (hs : c.IsSymm) : (pivotC c P d).IsSymm := by
  apply Matrix.IsSymm.ext
  intro i j
  have h : ∀ a b, c a b = c b a := fun a b => (hs.apply b a)
  simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply]
  by_cases hi : i = P <;> by_cases hj : j = P
  · subst hi; subst hj; rfl
  · subst hi; simp only [hj, if_true, if_false]
    rw [h j i]; ring
  · subst hj; simp only [hi, if_true, if_false]
    rw [h i j]; ring
  · simp only [hi, hj, if_false]
    rw [h j i, h j P, h i P]; ring

theorem pivotC_cleanP {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (P : Fin (N + 1))
    (hpp : c P P ≠ 0) (l : Fin (N + 1)) (hl : l ≠ P) : pivotC c P (c P) P l = 0 := by
  simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, hl, if_true, if_false]
  field_simp
  ring

theorem pivotC_cleank {N : ℕ} (c : Matrix (Fin (N + 1)) (Fin (N + 1)) ℝ) (P k : Fin (N + 1))
    (hs : c.IsSymm) (hk : k ≠ P) (hrow : ∀ l, l ≠ k → c k l = 0) (l : Fin (N + 1))
    (hl : l ≠ k) : pivotC c P (c P) k l = 0 := by
  have hPk : c P k = 0 := by rw [hs.apply k P]; exact hrow P (Ne.symm hk)
  have hkP : c k P = 0 := hrow P (Ne.symm hk)
  simp only [pivotC, pivotCPrime, pivotE, Matrix.of_apply, hk, if_false]
  by_cases hlP : l = P
  · subst hlP; simp [hkP, hPk]
  · simp [hlP, hkP, hPk, hrow l hl]

theorem numFree_update_some {n N : ℕ} (T T' : Tableau n N) (p : Fin N) (q : Fin n)
    (hp : T.lab p = none) (h : T'.lab = Function.update T.lab p (some q)) :
    numFree T' + 1 = numFree T := by
  classical
  unfold numFree
  have : (Finset.univ.filter fun k : Fin N => T'.lab k = none) =
      (Finset.univ.filter fun k : Fin N => T.lab k = none).erase p := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase, h]
    by_cases hk : k = p
    · subst hk; simp
    · simp [hk]
  rw [this, Finset.card_erase_add_one]
  simp [hp]

end BealeFreeCountAux

open BealeFreeCountAux in
open BealeConvexMin.QuadSimplex in
theorem solution {n N : ℕ} (T : ℕ → BealeConvexMin.QuadSimplex.Tableau n N)
    (hsymm : (T 0).c.IsSymm)
    (hns : ¬ BealeConvexMin.QuadSimplex.IsStandardForm (T 0))
    (hstep : ∀ k < BealeConvexMin.QuadSimplex.numFree (T 0),
      BealeConvexMin.QuadSimplex.BealeStep (T k) (T (k + 1))) :
    ∃ i ≤ BealeConvexMin.QuadSimplex.numFree (T 0),
      (BealeConvexMin.QuadSimplex.IsStandardForm (T i) ∨
        BealeConvexMin.QuadSimplex.numFree (T i) < BealeConvexMin.QuadSimplex.numFree (T 0)) ∧
      ∀ i' ≤ i, BealeConvexMin.QuadSimplex.numFree (T i') ≤
        BealeConvexMin.QuadSimplex.numFree (T 0) := by
  classical
  set s0 := numFree (T 0) with hs0
  have key : ∀ k ≤ s0,
      (∃ i ≤ k, (IsStandardForm (T i) ∨ numFree (T i) < s0) ∧ ∀ i' ≤ i, numFree (T i') ≤ s0) ∨
      ((∀ j ≤ k, numFree (T j) = s0) ∧ (T k).c.IsSymm ∧
        k ≤ (Finset.univ.filter fun m => Clean (T k) m).card) := by
    intro k
    induction k with
    | zero =>
      intro _
      right
      refine ⟨fun j hj => ?_, hsymm, Nat.zero_le _⟩
      rw [Nat.le_zero.mp hj]
    | succ k ih =>
      intro hk
      rcases ih (Nat.le_of_succ_le hk) with ⟨i, hi, hgood⟩ | ⟨hall, hsy, hcard⟩
      · exact Or.inl ⟨i, Nat.le_succ_of_le hi, hgood⟩
      by_cases hsf : IsStandardForm (T k)
      · exact Or.inl ⟨k, Nat.le_succ k, Or.inl hsf, fun i' hi' => (hall i' hi').le⟩
      obtain ⟨p, ⟨hprof, hfree⟩, hbr⟩ := hstep k hk
      have hex : ∃ k' : Fin N, (T k).lab k' = none ∧ (T k).c k'.succ 0 ≠ 0 := by
        by_contra hc
        push Not at hc
        exact hsf hc
      have hpnone : (T k).lab p = none := hfree hex
      have hpc : (T k).c p.succ 0 ≠ 0 := by
        rcases hprof with h | h
        · exact h.2
        · exact absurd hpnone h.1
      rcases hbr with ⟨q, _, _, hT'⟩ | ⟨hpos, _, hT'⟩
      · -- restricted variable enters: s drops
        have hlab : (T (k + 1)).lab = Function.update (T k).lab p (some q) := by
          rw [hT']; simp only [pivotTableau, orient_lab]
        have hnf := numFree_update_some (T k) (T (k + 1)) p q hpnone hlab
        have hk0 : numFree (T k) = s0 := hall k le_rfl
        left
        refine ⟨k + 1, le_rfl, Or.inr (by omega), fun i' hi' => ?_⟩
        rcases Nat.lt_or_eq_of_le hi' with h | h
        · exact (hall i' (Nat.lt_succ_iff.mp h)).le
        · subst h; omega
      · -- free variable enters: s unchanged, one more clean slot
        set U := orient (T k) p with hU
        have hUsym : U.c.IsSymm := orient_symm (T k) p hsy
        have hlab : (T (k + 1)).lab = (T k).lab := by
          rw [hT']; simp only [pivotTableau]
          rw [orient_lab, ← hpnone, Function.update_eq_self]
        have hnf : numFree (T (k + 1)) = numFree (T k) := by
          unfold numFree; rw [hlab]
        have hc : (T (k + 1)).c = pivotC U.c p.succ (U.c p.succ) := by rw [hT']; rfl
        right
        refine ⟨fun j hj => ?_, ?_, ?_⟩
        · rcases Nat.lt_or_eq_of_le hj with h | h
          · exact hall j (Nat.lt_succ_iff.mp h)
          · subst h; rw [hnf]; exact hall k le_rfl
        · rw [hc]; exact pivotC_symm _ _ _ hUsym
        · have hpnot : p ∉ (Finset.univ.filter fun m => Clean (T k) m) := by
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            intro hcl
            exact hpc (hcl.2 0 (Fin.succ_ne_zero p).symm)
          have hsub : insert p (Finset.univ.filter fun m => Clean (T k) m) ⊆
              (Finset.univ.filter fun m => Clean (T (k + 1)) m) := by
            intro m hm
            simp only [Finset.mem_insert, Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
            rcases hm with rfl | hm
            · refine ⟨by rw [hlab]; exact hpnone, fun l hl => ?_⟩
              rw [hc]; exact pivotC_cleanP _ _ (ne_of_gt hpos) l hl
            · have hmU : Clean U m := orient_clean (T k) p m hm
              refine ⟨by rw [hlab]; exact hm.1, fun l hl => ?_⟩
              have hmp : m ≠ p := by rintro rfl; exact hpnot (by simpa using hm)
              rw [hc]
              exact pivotC_cleank _ _ _ hUsym (fun h => hmp (Fin.succ_injective _ h))
                hmU.2 l hl
          have := Finset.card_le_card hsub
          rw [Finset.card_insert_of_notMem hpnot] at this
          omega
  rcases key s0 le_rfl with h | ⟨hall, _, hcard⟩
  · exact h
  · refine ⟨s0, le_rfl, Or.inl ?_, fun i' hi' => (hall i' hi').le⟩
    have hsub : (Finset.univ.filter fun m => Clean (T s0) m) ⊆
        (Finset.univ.filter fun m : Fin N => (T s0).lab m = none) := by
      intro m hm
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hm ⊢
      exact hm.1
    have hfc : (Finset.univ.filter fun m : Fin N => (T s0).lab m = none).card = s0 :=
      hall s0 le_rfl
    have heq := Finset.eq_of_subset_of_card_le hsub (by omega)
    intro m hm
    have hmem : m ∈ (Finset.univ.filter fun m : Fin N => (T s0).lab m = none) := by
      simp [hm]
    rw [← heq] at hmem
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hmem
    exact hmem.2 0 (Fin.succ_ne_zero m).symm
