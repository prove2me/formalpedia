-- Prove2me | solution 1 for DetANN.Thm11.outer_small
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-23T21:58:46.269799+00:00
-- url     : https://prove2.me/submissions/dcd51509-3b2e-4123-802c-0bb3cd967195

import Definitions.Def_DetANN_Thm11_OuterProg
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

/-! The case $n = 1$ of the outer programs of Theorem 1.1 (`outer_small`): preprocessing halts within
8 steps without storing, and every query halts within 5 steps with answer 0. -/


-- ===== BB_Pre =====
/-! Preorder theory of a `BSP`: nodes in preorder, subtrees as index intervals, and `balance`
in index terms (component counts, centroid as a first-argmin scan). -/

namespace DetANN.HPIM.BB

open DetANN.HPIM

variable {m : ℕ}

/-- The number of nodes. -/
def size : BSP m → ℕ
  | .leaf .. => 1
  | .cut _ _ l r => 1 + size l + size r

/-- The nodes in preorder: (path, subtree). -/
def pl : BSP m → List (List Bool × BSP m)
  | .leaf lo hi a => [([], .leaf lo hi a)]
  | .cut lo hi l r => ([], .cut lo hi l r) ::
      ((pl l).map (fun e => (false :: e.1, e.2)) ++ (pl r).map (fun e => (true :: e.1, e.2)))

lemma size_pos (T : BSP m) : 1 ≤ size T := by
  cases T <;> simp only [size] <;> omega

lemma pl_length (T : BSP m) : (pl T).length = size T := by
  induction T with
  | leaf => rfl
  | cut lo hi l r ihl ihr =>
    simp only [pl, List.length_cons, List.length_append, List.length_map, ihl, ihr, size]; omega

/-- The node at preorder index `i`. -/
def nd (T : BSP m) (i : ℕ) : List Bool × BSP m := ((pl T)[i]?).getD ([], T)

/-- Its path. -/
def P (T : BSP m) (i : ℕ) : List Bool := (nd T i).1
/-- Its subtree. -/
def U (T : BSP m) (i : ℕ) : BSP m := (nd T i).2
/-- The size of its subtree. -/
def S (T : BSP m) (i : ℕ) : ℕ := size (U T i)

lemma nd_some (T : BSP m) (i : ℕ) (h : i < size T) : (pl T)[i]? = some (nd T i) := by
  unfold nd
  rw [List.getElem?_eq_getElem (by rw [pl_length]; exact h)]
  rfl

lemma nd_zero (T : BSP m) : nd T 0 = ([], T) := by
  cases T <;> rfl

lemma nd_left (lo hi : Fin m → ℝ) (l r : BSP m) (i : ℕ) (h : i < size l) :
    nd (.cut lo hi l r) (1 + i) = (false :: (nd l i).1, (nd l i).2) := by
  unfold nd
  rw [show 1 + i = i + 1 by omega]
  simp only [pl, List.getElem?_cons_succ]
  rw [List.getElem?_append_left (by rw [List.length_map, pl_length]; exact h), List.getElem?_map,
    nd_some l i h]
  rfl

lemma nd_right (lo hi : Fin m → ℝ) (l r : BSP m) (i : ℕ) (h : i < size r) :
    nd (.cut lo hi l r) (1 + size l + i) = (true :: (nd r i).1, (nd r i).2) := by
  unfold nd
  rw [show 1 + size l + i = (size l + i) + 1 by omega]
  simp only [pl, List.getElem?_cons_succ]
  rw [List.getElem?_append_right (by rw [List.length_map, pl_length]; omega), List.length_map,
    pl_length, show size l + i - size l = i by omega, List.getElem?_map, nd_some r i h]
  rfl

lemma cut_cases (a b i : ℕ) (h : i < 1 + a + b) :
    i = 0 ∨ (∃ i', i' < a ∧ i = 1 + i') ∨ (∃ i', i' < b ∧ i = 1 + a + i') := by
  by_cases h0 : i = 0
  · exact Or.inl h0
  · by_cases h1 : i < 1 + a
    · exact Or.inr (Or.inl ⟨i - 1, by omega, by omega⟩)
    · exact Or.inr (Or.inr ⟨i - 1 - a, by omega, by omega⟩)

lemma P_zero (T : BSP m) : P T 0 = [] := by unfold P; rw [nd_zero]
lemma U_zero (T : BSP m) : U T 0 = T := by unfold U; rw [nd_zero]

lemma S_zero (T : BSP m) : S T 0 = size T := by unfold S; rw [U_zero]

/-- Subtrees stay inside the tree. -/
lemma bound (T : BSP m) : ∀ i, i < size T → i + S T i ≤ size T := by
  induction T with
  | leaf lo hi a =>
    intro i hi; simp only [size] at hi
    rw [show i = 0 by omega, S_zero]; simp [size]
  | cut lo hi l r ihl ihr =>
    intro i hi'
    rcases cut_cases (size l) (size r) i (by simpa [size] using hi') with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
    · subst h; rw [S_zero]; omega
    · have := ihl i' h1
      unfold S U at this ⊢; rw [nd_left lo hi l r i' h1]; simp only [size]; omega
    · have := ihr i' h1
      unfold S U at this ⊢; rw [nd_right lo hi l r i' h1]; simp only [size]; omega

/-- The subtree at the path of node `i` is `U T i`. -/
lemma sub_P (T : BSP m) : ∀ i, i < size T → T.sub (P T i) = some (U T i) := by
  induction T with
  | leaf lo hi a =>
    intro i hi; simp only [size] at hi
    rw [show i = 0 by omega, P_zero, U_zero]; rfl
  | cut lo hi l r ihl ihr =>
    intro i hi'
    rcases cut_cases (size l) (size r) i (by simpa [size] using hi') with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
    · subst h; rw [P_zero, U_zero]; rfl
    · unfold P U; rw [nd_left lo hi l r i' h1]
      simp only [BSP.sub]; exact ihl i' h1
    · unfold P U; rw [nd_right lo hi l r i' h1]
      simp only [BSP.sub]; exact ihr i' h1

/-- **Subtrees are intervals.** -/
lemma prefix_iff (T : BSP m) : ∀ i k, i < size T → k < size T →
    (P T i <+: P T k ↔ i ≤ k ∧ k < i + S T i) := by
  induction T with
  | leaf lo hi a =>
    intro i k hi hk; simp only [size] at hi hk
    rw [show i = 0 by omega, show k = 0 by omega, P_zero, S_zero]; simp [size]
  | cut lo hi l r ihl ihr =>
    intro i k hi' hk'
    have hs : size (BSP.cut lo hi l r) = 1 + size l + size r := rfl
    rcases cut_cases (size l) (size r) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
    · subst h; rw [P_zero, S_zero]; simp only [List.nil_prefix, true_iff]; omega
    · have hb := bound l i' h1
      rcases cut_cases (size l) (size r) k (by omega) with h | ⟨k', h2, rfl⟩ | ⟨k', h2, rfl⟩
      · subst h; unfold P S U; rw [nd_left lo hi l r i' h1, nd_zero]
        simp only [List.prefix_nil, reduceCtorEq, false_iff]; omega
      · have := ihl i' k' h1 h2
        unfold P S U at this ⊢; rw [nd_left lo hi l r i' h1, nd_left lo hi l r k' h2]
        simp only [List.cons_prefix_cons, true_and]; rw [this]; omega
      · unfold P S U at hb ⊢; rw [nd_left lo hi l r i' h1, nd_right lo hi l r k' h2]
        simp only [List.cons_prefix_cons, Bool.false_eq_true, false_and, false_iff]; omega
    · have hb := bound r i' h1
      rcases cut_cases (size l) (size r) k (by omega) with h | ⟨k', h2, rfl⟩ | ⟨k', h2, rfl⟩
      · subst h; unfold P S U; rw [nd_right lo hi l r i' h1, nd_zero]
        simp only [List.prefix_nil, reduceCtorEq, false_iff]; omega
      · unfold P S U; rw [nd_right lo hi l r i' h1, nd_left lo hi l r k' h2]
        simp only [List.cons_prefix_cons, Bool.true_eq_false, false_and, false_iff]; omega
      · have := ihr i' k' h1 h2
        unfold P S U at this ⊢; rw [nd_right lo hi l r i' h1, nd_right lo hi l r k' h2]
        simp only [List.cons_prefix_cons, true_and]; rw [this]; omega

/-- **Preorder is the path order.** -/
lemma P_lt (T : BSP m) : ∀ i k, i < k → k < size T → P T i < P T k := by
  induction T with
  | leaf lo hi a => intro i k hik hk; simp only [size] at hk; omega
  | cut lo hi l r ihl ihr =>
    intro i k hik hk'
    have hs : size (BSP.cut lo hi l r) = 1 + size l + size r := rfl
    rcases cut_cases (size l) (size r) k (by omega) with h | ⟨k', h2, rfl⟩ | ⟨k', h2, rfl⟩
    · omega
    · rcases cut_cases (size l) (size r) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
      · subst h; rw [P_zero]; unfold P; rw [nd_left lo hi l r k' h2]; exact List.nil_lt_cons _ _
      · have := ihl i' k' (by omega) h2
        unfold P at this ⊢; rw [nd_left lo hi l r i' h1, nd_left lo hi l r k' h2]
        exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, this⟩)
      · omega
    · rcases cut_cases (size l) (size r) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
      · subst h; rw [P_zero]; unfold P; rw [nd_right lo hi l r k' h2]; exact List.nil_lt_cons _ _
      · unfold P; rw [nd_left lo hi l r i' h1, nd_right lo hi l r k' h2]
        exact List.cons_lt_cons_iff.2 (Or.inl (by decide))
      · have := ihr i' k' (by omega) h2
        unfold P at this ⊢; rw [nd_right lo hi l r i' h1, nd_right lo hi l r k' h2]
        exact List.cons_lt_cons_iff.2 (Or.inr ⟨rfl, this⟩)

lemma P_le (T : BSP m) (i k : ℕ) (h : i ≤ k) (hk : k < size T) : P T i ≤ P T k := by
  rcases Nat.eq_or_lt_of_le h with rfl | h
  · exact le_rfl
  · exact (P_lt T i k h hk).le

lemma P_inj (T : BSP m) (i k : ℕ) (hi : i < size T) (hk : k < size T) (h : P T i = P T k) : i = k := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h' | h'
  · exact absurd h (P_lt T i k h' hk).ne
  · exact absurd h.symm (P_lt T k i h' hi).ne

lemma mem_paths (T : BSP m) : ∀ x, x ∈ T.paths ↔ ∃ i < size T, P T i = x := by
  induction T with
  | leaf lo hi a =>
    intro x; simp only [BSP.paths, Finset.mem_singleton, size]
    constructor
    · rintro rfl; exact ⟨0, by omega, P_zero _⟩
    · rintro ⟨i, hi, rfl⟩; rw [show i = 0 by omega, P_zero]
  | cut lo hi l r ihl ihr =>
    intro x
    have hs : size (BSP.cut lo hi l r) = 1 + size l + size r := rfl
    simp only [BSP.paths, Finset.mem_insert, Finset.mem_union, Finset.mem_image, ihl, ihr]
    constructor
    · rintro (rfl | ⟨y, ⟨i, hi2, rfl⟩, rfl⟩ | ⟨y, ⟨i, hi2, rfl⟩, rfl⟩)
      · exact ⟨0, by omega, P_zero _⟩
      · refine ⟨1 + i, by omega, ?_⟩; unfold P; rw [nd_left lo hi l r i hi2]
      · refine ⟨1 + size l + i, by omega, ?_⟩; unfold P; rw [nd_right lo hi l r i hi2]
    · rintro ⟨i, hi', rfl⟩
      rcases cut_cases (size l) (size r) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
      · subst h; exact Or.inl (P_zero _)
      · refine Or.inr (Or.inl ⟨P l i', ⟨i', h1, rfl⟩, ?_⟩); unfold P; rw [nd_left lo hi l r i' h1]
      · refine Or.inr (Or.inr ⟨P r i', ⟨i', h1, rfl⟩, ?_⟩); unfold P; rw [nd_right lo hi l r i' h1]

lemma paths_card (T : BSP m) : T.paths.card = size T := by
  have : T.paths = (Finset.range (size T)).image (P T) := by
    ext x; simp only [mem_paths, Finset.mem_image, Finset.mem_range]
  rw [this, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi k hk h
  exact P_inj T i k (Finset.mem_range.1 hi) (Finset.mem_range.1 hk) h

/-- The children of a cut node in preorder. -/
lemma children (T : BSP m) : ∀ i, i < size T → ∀ lo hi l r, U T i = .cut lo hi l r →
    U T (i + 1) = l ∧ U T (i + 1 + size l) = r := by
  induction T with
  | leaf lo hi a =>
    intro i hi; simp only [size] at hi
    rw [show i = 0 by omega, U_zero]; intro _ _ _ _ h; cases h
  | cut lo hi L R ihl ihr =>
    intro i hi'
    have hs : size (BSP.cut lo hi L R) = 1 + size L + size R := rfl
    rcases cut_cases (size L) (size R) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
    · subst h; rw [U_zero]; intro lo' hi'' l r h
      simp only [BSP.cut.injEq] at h
      obtain ⟨-, -, h3, h4⟩ := h
      rw [← h3, ← h4]
      constructor
      · unfold U; rw [show 0 + 1 = 1 + 0 by rfl, nd_left lo hi L R 0 (size_pos L), nd_zero]
      · unfold U; rw [show 0 + 1 + size L = 1 + size L + 0 by omega, nd_right lo hi L R 0 (size_pos R),
          nd_zero]
    · intro lo' hi'' l r h
      have hb := bound L i' h1
      unfold S at hb
      unfold U at h; rw [nd_left lo hi L R i' h1] at h
      have hU : U L i' = .cut lo' hi'' l r := h
      rw [hU] at hb; simp only [size] at hb
      have := size_pos l; have := size_pos r
      obtain ⟨e1, e2⟩ := ihl i' h1 lo' hi'' l r hU
      constructor
      · unfold U at e1 ⊢; rw [show 1 + i' + 1 = 1 + (i' + 1) by omega, nd_left lo hi L R _ (by omega)]
        exact e1
      · unfold U at e2 ⊢
        rw [show 1 + i' + 1 + size l = 1 + (i' + 1 + size l) by omega, nd_left lo hi L R _ (by omega)]
        exact e2
    · intro lo' hi'' l r h
      have hb := bound R i' h1
      unfold S at hb
      unfold U at h; rw [nd_right lo hi L R i' h1] at h
      have hU : U R i' = .cut lo' hi'' l r := h
      rw [hU] at hb; simp only [size] at hb
      have := size_pos l; have := size_pos r
      obtain ⟨e1, e2⟩ := ihr i' h1 lo' hi'' l r hU
      constructor
      · unfold U at e1 ⊢
        rw [show 1 + size L + i' + 1 = 1 + size L + (i' + 1) by omega, nd_right lo hi L R _ (by omega)]
        exact e1
      · unfold U at e2 ⊢
        rw [show 1 + size L + i' + 1 + size l = 1 + size L + (i' + 1 + size l) by omega,
          nd_right lo hi L R _ (by omega)]
        exact e2

/-- The size recursion used by the machine. -/
lemma S_cut (T : BSP m) (i : ℕ) (hi : i < size T) (lo hi' : Fin m → ℝ) (l r : BSP m)
    (h : U T i = .cut lo hi' l r) :
    S T i = 1 + S T (i + 1) + S T (i + 1 + S T (i + 1)) := by
  obtain ⟨e1, e2⟩ := children T i hi lo hi' l r h
  unfold S; rw [e1, e2, h]; rfl

/-! ### Components and centroids in index terms -/

/-- Node `k` is not below a removed node. -/
def unc (T : BSP m) (R : Finset (List Bool)) (k : ℕ) : Prop := ∀ c ∈ R, ¬ c <+: P T k

instance instDecUnc (T : BSP m) (R : Finset (List Bool)) : DecidablePred (unc T R) :=
  fun k => by unfold unc; infer_instance

/-- The size of the component of node `i`. -/
def cntI (T : BSP m) (R : Finset (List Bool)) (i : ℕ) : ℕ :=
  ((Finset.Ico i (i + S T i)).filter (unc T R)).card

lemma comp_eq (T : BSP m) (R : Finset (List Bool)) (j : ℕ) (hj : j < size T) :
    comp T (P T j) R = ((Finset.Ico j (j + S T j)).filter (unc T R)).image (P T) := by
  have hb := bound T j hj
  ext x
  simp only [comp, Finset.mem_filter, mem_paths, Finset.mem_image, Finset.mem_Ico, unc]
  constructor
  · rintro ⟨⟨k, hk, rfl⟩, hp, hR⟩
    exact ⟨k, ⟨(prefix_iff T j k hj hk).1 hp, hR⟩, rfl⟩
  · rintro ⟨k, ⟨hk, hR⟩, rfl⟩
    exact ⟨⟨k, by omega, rfl⟩, (prefix_iff T j k hj (by omega)).2 hk, hR⟩

lemma comp_card (T : BSP m) (R : Finset (List Bool)) (j : ℕ) (hj : j < size T) :
    (comp T (P T j) R).card = cntI T R j := by
  have hb := bound T j hj
  rw [comp_eq T R j hj, Finset.card_image_of_injOn]
  · rfl
  intro i hi k hk h
  simp only [Finset.coe_filter, Finset.mem_Ico, Set.mem_setOf_eq] at hi hk
  exact P_inj T i k (by omega) (by omega) h

/-- The component count recursion used by the machine. -/
lemma cnt_cut (T : BSP m) (R : Finset (List Bool)) (i : ℕ) (hi : i < size T) (lo hi' : Fin m → ℝ)
    (l r : BSP m) (h : U T i = .cut lo hi' l r) :
    cntI T R i = (if unc T R i then 1 else 0) + cntI T R (i + 1) + cntI T R (i + 1 + S T (i + 1)) := by
  have hS := S_cut T i hi lo hi' l r h
  unfold cntI
  simp only [Finset.card_filter]
  rw [hS, ← Finset.sum_Ico_consecutive _ (show i ≤ i + 1 by omega)
    (show i + 1 ≤ i + (1 + S T (i + 1) + S T (i + 1 + S T (i + 1))) by omega),
    ← Finset.sum_Ico_consecutive _ (show i + 1 ≤ i + 1 + S T (i + 1) by omega)
    (show i + 1 + S T (i + 1) ≤ i + (1 + S T (i + 1) + S T (i + 1 + S T (i + 1))) by omega)]
  rw [Finset.sum_Ico_succ_top (le_refl i), Finset.Ico_self, Finset.sum_empty, zero_add]
  rw [show i + (1 + S T (i + 1) + S T (i + 1 + S T (i + 1))) =
    i + 1 + S T (i + 1) + S T (i + 1 + S T (i + 1)) by omega]
  ring

lemma cnt_leaf (T : BSP m) (R : Finset (List Bool)) (i : ℕ) (lo hi' : Fin m → ℝ) (a : Option ℕ)
    (h : U T i = .leaf lo hi' a) : cntI T R i = if unc T R i then 1 else 0 := by
  unfold cntI S; rw [h]; simp only [size]
  rw [Finset.card_filter, Finset.sum_Ico_succ_top (le_refl i), Finset.Ico_self, Finset.sum_empty,
    zero_add]

lemma unc_insert (T : BSP m) (R : Finset (List Bool)) (c k : ℕ) (hc : c < size T) (hk : k < size T) :
    unc T (insert (P T c) R) k ↔ unc T R k ∧ ¬ (c ≤ k ∧ k < c + S T c) := by
  unfold unc
  rw [← prefix_iff T c k hc hk]
  simp only [Finset.mem_insert, forall_eq_or_imp]
  tauto

/-- The interval of a node inside the interval of an ancestor. -/
lemma sub_interval (T : BSP m) (j c : ℕ) (hj : j < size T) (h1 : j ≤ c) (h2 : c < j + S T j) :
    c + S T c ≤ j + S T j := by
  have hb := bound T j hj
  have hc : c < size T := by omega
  have hbc := bound T c hc
  have hpos : 1 ≤ S T c := size_pos _
  have hjc := (prefix_iff T j c hj hc).2 ⟨h1, h2⟩
  have hx := (prefix_iff T c (c + S T c - 1) hc (by omega)).2 ⟨by omega, by omega⟩
  have := (prefix_iff T j (c + S T c - 1) hj (by omega)).1 (hjc.trans hx)
  omega

lemma cnt_le (T : BSP m) (R : Finset (List Bool)) (j c : ℕ) (hj : j < size T) (h1 : j ≤ c)
    (h2 : c < j + S T j) : cntI T R c ≤ cntI T R j := by
  have := sub_interval T j c hj h1 h2
  unfold cntI
  apply Finset.card_le_card
  intro x hx; simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
  exact ⟨⟨by omega, by omega⟩, hx.2⟩

/-- Removing the subtree of `c` splits the component of `j`. -/
lemma cnt_split (T : BSP m) (R : Finset (List Bool)) (j c : ℕ) (hj : j < size T) (h1 : j < c)
    (h2 : c < j + S T j) :
    cntI T R j = cntI T R c + cntI T (insert (P T c) R) j := by
  have hsub := sub_interval T j c hj h1.le h2
  have hb := bound T j hj
  unfold cntI
  rw [← Finset.card_filter_add_card_filter_not (fun k => c ≤ k ∧ k < c + S T c)]
  congr 1
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨_, h⟩, h'⟩; exact ⟨h', h⟩
    · rintro ⟨h', h⟩; exact ⟨⟨by omega, h⟩, h'⟩
  · congr 1; ext x; simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · rintro ⟨⟨hx, h⟩, h'⟩
      exact ⟨hx, (unc_insert T R c x (by omega) (by omega)).2 ⟨h, h'⟩⟩
    · rintro ⟨hx, h⟩
      have := (unc_insert T R c x (by omega) (by omega)).1 h
      exact ⟨⟨hx, this.1⟩, this.2⟩

/-! ### The first-argmin scan -/

/-- The candidates of the centroid of `j`. -/
def candsI (T : BSP m) (R : Finset (List Bool)) (j : ℕ) : Finset ℕ :=
  (Finset.Ico (j + 1) (j + S T j)).filter (unc T R)

/-- The score of candidate `k` in the component of `j`. -/
def score (T : BSP m) (R : Finset (List Bool)) (j k : ℕ) : ℕ :=
  max (cntI T R k) (cntI T R j - cntI T R k)

/-- The scan invariant after the indices `[lo, i)`: `bs = M` and no candidate so far, or `b` is the
first candidate of least score. -/
def SInv (cand : ℕ → Prop) (sc : ℕ → ℕ) (M lo i b bs : ℕ) : Prop :=
  (bs = M ∧ ∀ k, lo ≤ k → k < i → ¬ cand k) ∨
    (lo ≤ b ∧ b < i ∧ cand b ∧ bs = sc b ∧ ∀ k, lo ≤ k → k < i → cand k → sc b ≤ sc k ∧ (sc k = sc b → b ≤ k))

lemma sinv_start (cand : ℕ → Prop) (sc : ℕ → ℕ) (M lo b : ℕ) : SInv cand sc M lo lo b M :=
  Or.inl ⟨rfl, fun k h1 h2 => by omega⟩

lemma sinv_skip (cand : ℕ → Prop) (sc : ℕ → ℕ) (M lo i b bs : ℕ) (h : SInv cand sc M lo i b bs)
    (hlo : lo ≤ i) (hb : ∀ k, cand k → sc k < M)
    (hn : ¬ cand i ∨ bs ≤ sc i) : SInv cand sc M lo (i + 1) b bs := by
  rcases h with ⟨e, h⟩ | ⟨h1, h2, h3, h4, h5⟩
  · left; refine ⟨e, fun k k1 k2 hk => ?_⟩
    rcases Nat.lt_or_ge k i with k3 | k3
    · exact h k k1 k3 hk
    · have : k = i := by omega
      subst this
      rcases hn with hn | hn
      · exact hn hk
      · have := hb k hk; omega
  · right; refine ⟨h1, by omega, h3, h4, fun k k1 k2 hk => ?_⟩
    rcases Nat.lt_or_ge k i with k3 | k3
    · exact h5 k k1 k3 hk
    · have : k = i := by omega
      subst this
      rcases hn with hn | hn
      · exact absurd hk hn
      · constructor
        · omega
        · intro e; omega

lemma sinv_take (cand : ℕ → Prop) (sc : ℕ → ℕ) (M lo i b bs : ℕ) (h : SInv cand sc M lo i b bs)
    (hlo : lo ≤ i) (hb : ∀ k, cand k → sc k < M) (hc : cand i) (hs : sc i < bs) :
    SInv cand sc M lo (i + 1) i (sc i) := by
  right
  refine ⟨hlo, by omega, hc, rfl, fun k k1 k2 hk => ?_⟩
  rcases Nat.lt_or_ge k i with k3 | k3
  · rcases h with ⟨e, h⟩ | ⟨h1, h2, h3, h4, h5⟩
    · exact absurd hk (h k k1 k3)
    · have := h5 k k1 k3 hk; omega
  · have : k = i := by omega
    subst this; exact ⟨le_rfl, fun _ => le_rfl⟩

lemma sinv_end (cand : ℕ → Prop) [DecidablePred cand] (sc : ℕ → ℕ) (M lo hi b bs : ℕ)
    (h : SInv cand sc M lo hi b bs) (hb : ∀ k, cand k → sc k < M)
    (hne : ((Finset.Ico lo hi).filter cand).Nonempty) :
    b ∈ (Finset.Ico lo hi).filter cand ∧ (∀ k ∈ (Finset.Ico lo hi).filter cand, sc b ≤ sc k) ∧
      ∀ k ∈ (Finset.Ico lo hi).filter cand, sc k = sc b → b ≤ k := by
  rcases h with ⟨e, h⟩ | ⟨h1, h2, h3, h4, h5⟩
  · exfalso
    obtain ⟨k, hk⟩ := hne
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk
    exact h k hk.1.1 hk.1.2 hk.2
  · refine ⟨by simp only [Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨h1, h2⟩, h3⟩, ?_, ?_⟩
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_Ico] at hk
      exact (h5 k hk.1.1 hk.1.2 hk.2).1
    · intro k hk; simp only [Finset.mem_filter, Finset.mem_Ico] at hk
      exact (h5 k hk.1.1 hk.1.2 hk.2).2

/-- The centroid in index terms: the first candidate of least score. -/
lemma centroid_eq (T : BSP m) (R : Finset (List Bool)) (j b : ℕ) (hj : j < size T)
    (hb : b ∈ candsI T R j) (hmin : ∀ k ∈ candsI T R j, score T R j b ≤ score T R j k)
    (hfirst : ∀ k ∈ candsI T R j, score T R j k = score T R j b → b ≤ k) :
    centroid T (P T j) R = some (P T b) := by
  have hbd := bound T j hj
  have hmemI : ∀ k, k ∈ candsI T R j → k < size T := by
    intro k hk; simp only [candsI, Finset.mem_filter, Finset.mem_Ico] at hk; omega
  -- the candidates as paths
  have hC : (comp T (P T j) R).erase (P T j) = (candsI T R j).image (P T) := by
    rw [comp_eq T R j hj]
    ext x
    simp only [Finset.mem_erase, Finset.mem_image, Finset.mem_filter, Finset.mem_Ico, candsI]
    constructor
    · rintro ⟨hne, k, ⟨⟨k1, k2⟩, hk⟩, rfl⟩
      refine ⟨k, ⟨⟨?_, k2⟩, hk⟩, rfl⟩
      rcases Nat.eq_or_lt_of_le k1 with e | e
      · exact absurd (by rw [e]) hne
      · omega
    · rintro ⟨k, ⟨⟨k1, k2⟩, hk⟩, rfl⟩
      refine ⟨fun e => ?_, k, ⟨⟨by omega, k2⟩, hk⟩, rfl⟩
      have := P_inj T k j (by omega) hj e; omega
  have hsc : ∀ k ∈ candsI T R j,
      max (comp T (P T k) R).card ((comp T (P T j) R).card - (comp T (P T k) R).card) =
        score T R j k := by
    intro k hk; rw [comp_card T R k (hmemI k hk), comp_card T R j hj]; rfl
  unfold centroid
  simp only []
  rw [hC]
  have hne : ((candsI T R j).image (P T)).Nonempty := ⟨P T b, Finset.mem_image_of_mem _ hb⟩
  rw [dif_pos hne]
  -- the least score
  have hinf : ((candsI T R j).image (P T)).inf' hne
      (fun c => max (comp T c R).card ((comp T (P T j) R).card - (comp T c R).card)) =
      score T R j b := by
    apply le_antisymm
    · rw [← hsc b hb]; exact Finset.inf'_le _ (Finset.mem_image_of_mem _ hb)
    · apply Finset.le_inf'
      intro y hy
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
      rw [hsc k hk]; exact hmin k hk
  have hbest : P T b ∈ ((candsI T R j).image (P T)).filter (fun c =>
      max (comp T c R).card ((comp T (P T j) R).card - (comp T c R).card) =
        ((candsI T R j).image (P T)).inf' hne
          (fun c => max (comp T c R).card ((comp T (P T j) R).card - (comp T c R).card))) := by
    rw [Finset.mem_filter, hinf, hsc b hb]
    exact ⟨Finset.mem_image_of_mem _ hb, rfl⟩
  rw [dif_pos ⟨_, hbest⟩]
  congr 1
  apply le_antisymm
  · exact Finset.min'_le _ _ hbest
  · apply Finset.le_min'
    intro y hy
    rw [Finset.mem_filter, hinf] at hy
    obtain ⟨hy1, hy2⟩ := hy
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy1
    rw [hsc k hk] at hy2
    have hbk := hfirst k hk hy2
    exact P_le T b k hbk (hmemI k hk)

/-- **One step of `balance` in index terms.** -/
lemma balance_succ (T : BSP m) (R : Finset (List Bool)) (f j b : ℕ) (hj : j < size T)
    (hb : 2 ≤ cntI T R j → b ∈ candsI T R j ∧ (∀ k ∈ candsI T R j, score T R j b ≤ score T R j k) ∧
      (∀ k ∈ candsI T R j, score T R j k = score T R j b → b ≤ k)) :
    balance T (f + 1) (P T j) R =
      if cntI T R j ≤ 1 then .leaf (U T j).ans else
        .test (U T b).box.1 (U T b).box.2 (balance T f (P T b) R)
          (balance T f (P T j) (insert (P T b) R)) := by
  rw [balance, comp_card T R j hj, sub_P T j hj]
  by_cases h : cntI T R j ≤ 1
  · rw [if_pos h, if_pos h]; rfl
  · rw [if_neg h, if_neg h]
    obtain ⟨h1, h2, h3⟩ := hb (by omega)
    have hbn : b < size T := by
      simp only [candsI, Finset.mem_filter, Finset.mem_Ico] at h1; have := bound T j hj; omega
    rw [centroid_eq T R j b hj h1 h2 h3]
    simp only []
    rw [sub_P T b hbn]

end DetANN.HPIM.BB

-- ===== QP_Work =====
/-! Q' work file: the program and the stepping lemmas. -/

open PNormReg PNormRegLib SmaleNinth

namespace DetANN.HPIM.QP

lemma RAMStep_eq {R : RAMProgram} {s : RAMConfig} {i : RAMInstr} (h : R[s.pc]? = some i) :
    RAMStep R s = coreExec i s := by
  simp only [RAMStep, h]
  cases i <;> rfl

lemma core_get {P : Program} {pc : ℕ} {i : RAMInstr} (h : P[pc]? = some (.core i)) :
    (coreProgram P)[pc]? = some i := by
  simp [coreProgram, List.getElem?_map, h]

lemma step_eq_exec (P : Program) (ω : ℕ → Bool) (s : State) (ins : Instr)
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) : step P ω s = exec ω ins s := by
  cases ins with
  | core i => simp [step, exec, hh, h, RAMStep_eq (core_get h)]
  | _ => simp [step, exec, hh, h]

lemma run_succ (P : Program) (s : State) (ω : ℕ → Bool) (n : ℕ) :
    run P s ω (n + 1) = run P (step P ω s) ω n := by
  simp [run, Function.iterate_succ_apply]

lemma run_zero (P : Program) (s : State) (ω : ℕ → Bool) : run P s ω 0 = s := rfl

lemma run_add (P : Program) (s : State) (ω : ℕ → Bool) (a b : ℕ) :
    run P s ω (a + b) = run P (run P s ω a) ω b := by
  simp only [run]; rw [add_comm, Function.iterate_add_apply]

lemma run_exec {P : Program} {s : State} {ω : ℕ → Bool} {n : ℕ} {ins : Instr}
    (hh : s.halted = false) (h : P[s.core.pc]? = some ins) :
    run P s ω (n + 1) = run P (exec ω ins s) ω n := by
  rw [run_succ, step_eq_exec P ω s ins hh h]

/-- The query program. -/
def Qprog : Program := [
  .core (.pset 9 (0)), -- 0
  .core (.pset 19 (1)), -- 1
  .core (.pset 20 (2)), -- 2
  .core (.pset 4 (1)), -- 3
  .integerLoad 1 4, -- 4
  .core (.pset 4 (2)), -- 5
  .integerLoad 2 4, -- 6
  .integerLoad 18 2, -- 7
  .core (.pjle 18 9 76), -- 8
  .core (.pcopy 4 2), -- 9
  .core (.pinc 4), -- 10
  .integerLoad 12 4, -- 11
  .core (.pcopy 13 12), -- 12
  .core (.pdec 13), -- 13
  .core (.pjle 12 9 80), -- 14
  .core (.pset 17 (0)), -- 15
  .core (.pset 11 (0)), -- 16
  .core (.pjle 9 9 88), -- 17
  .core (.pjle 10 9 29), -- 18
  .core (.pcopy 4 2), -- 19
  .core (.pinc 4), -- 20
  .core (.pinc 4), -- 21
  .core (.pinc 4), -- 22
  .core (.pinc 4), -- 23
  .integerLoad 4 4, -- 24
  .core (.pdec 10), -- 25
  .pointerAdd 4 4 10, -- 26
  .integerLoad 2 4, -- 27
  .core (.pjle 9 9 7), -- 28
  .core (.pcopy 17 13), -- 29
  .core (.pset 11 (1)), -- 30
  .core (.pjle 9 9 88), -- 31
  .core (.pjle 10 9 80), -- 32
  .core (.pcopy 4 2), -- 33
  .core (.pinc 4), -- 34
  .core (.pinc 4), -- 35
  .core (.pinc 4), -- 36
  .core (.pinc 4), -- 37
  .core (.pinc 4), -- 38
  .core (.pinc 4), -- 39
  .integerLoad 14 4, -- 40
  .core (.pset 15 (0)), -- 41
  .core (.pjle 14 9 58), -- 42
  .core (.pdec 14), -- 43
  .core (.pset 4 (3)), -- 44
  .integerLoad 4 4, -- 45
  .pointerAdd 4 4 14, -- 46
  .integerLoad 21 4, -- 47
  .pointerAdd 16 15 21, -- 48
  .core (.pcopy 17 16), -- 49
  .core (.pjle 17 13 52), -- 50
  .core (.pcopy 17 13), -- 51
  .core (.pset 11 (2)), -- 52
  .core (.pjle 9 9 88), -- 53
  .core (.pjle 10 9 56), -- 54
  .core (.pjle 9 9 42), -- 55
  .core (.pcopy 15 16), -- 56
  .core (.pjle 9 9 42), -- 57
  .core (.pcopy 17 15), -- 58
  .core (.pinc 17), -- 59
  .core (.pjle 17 13 62), -- 60
  .core (.pcopy 17 13), -- 61
  .core (.pset 11 (3)), -- 62
  .core (.pjle 9 9 88), -- 63
  .core (.pjle 10 9 74), -- 64
  .core (.pcopy 4 2), -- 65
  .core (.pinc 4), -- 66
  .core (.pinc 4), -- 67
  .core (.pinc 4), -- 68
  .integerLoad 4 4, -- 69
  .core (.pdec 10), -- 70
  .pointerAdd 4 4 10, -- 71
  .integerLoad 0 4, -- 72
  .halt, -- 73
  .core (.pset 0 (0)), -- 74
  .halt, -- 75
  .core (.pcopy 4 2), -- 76
  .core (.pinc 4), -- 77
  .integerLoad 0 4, -- 78
  .halt, -- 79
  .core (.pcopy 4 2), -- 80
  .core (.pinc 4), -- 81
  .core (.pinc 4), -- 82
  .core (.pinc 4), -- 83
  .core (.pinc 4), -- 84
  .core (.pinc 4), -- 85
  .integerLoad 2 4, -- 86
  .core (.pjle 9 9 7), -- 87
  .core (.pcopy 4 2), -- 88
  .core (.pinc 4), -- 89
  .core (.pinc 4), -- 90
  .integerLoad 4 4, -- 91
  .pointerAdd 4 4 17, -- 92
  .integerLoad 3 4, -- 93
  .integerLoad 18 3, -- 94
  .core (.pjle 18 9 128), -- 95
  .core (.pcopy 4 3), -- 96
  .core (.pinc 4), -- 97
  .integerLoad 5 4, -- 98
  .pointerAdd 6 5 1, -- 99
  .core (.pset 7 (-1)), -- 100
  .core (.pcopy 8 1), -- 101
  .core (.pjle 8 9 117), -- 102
  .core (.load 0 5), -- 103
  .core (.load 1 7), -- 104
  .core (.sub 2 0 1), -- 105
  .core (.jle 2 108), -- 106
  .core (.pjle 9 9 122), -- 107
  .core (.load 0 6), -- 108
  .core (.sub 2 1 0), -- 109
  .core (.jle 2 112), -- 110
  .core (.pjle 9 9 122), -- 111
  .core (.pinc 5), -- 112
  .core (.pinc 6), -- 113
  .core (.pdec 7), -- 114
  .core (.pdec 8), -- 115
  .core (.pjle 9 9 102), -- 116
  .core (.pcopy 4 3), -- 117
  .core (.pinc 4), -- 118
  .core (.pinc 4), -- 119
  .integerLoad 3 4, -- 120
  .core (.pjle 9 9 94), -- 121
  .core (.pcopy 4 3), -- 122
  .core (.pinc 4), -- 123
  .core (.pinc 4), -- 124
  .core (.pinc 4), -- 125
  .integerLoad 3 4, -- 126
  .core (.pjle 9 9 94), -- 127
  .core (.pcopy 4 3), -- 128
  .core (.pinc 4), -- 129
  .integerLoad 10 4, -- 130
  .core (.pjle 11 9 18), -- 131
  .core (.pjle 11 19 32), -- 132
  .core (.pjle 11 20 54), -- 133
  .core (.pjle 9 9 64) -- 134
]

end DetANN.HPIM.QP

-- ===== PP_Ladder =====
/-! Pilot of the block format for the preprocessing program `P`: a block is a program
`blk off` with absolute jump targets `off + k`; its specification holds in every host `Q` that
embeds it at `off`. Pilot block: the radius ladder (`M`, `t₀`). -/

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP

/-- One step of a host `Q` through instruction `i` of an embedded block. -/
lemma run_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {ω : ℕ → Bool} {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i)
    (hB : B[i]? = some ins) : run Q s ω (n + 1) = run Q (exec ω ins s) ω n :=
  run_exec hh (by rw [hpc]; exact hE i ins hB)

/- A step through an embedded block (normalizes `pc = off + k`). -/

/-- **The ladder block.** In: real regs `40 = b`, `41 = ρ 0`, `42 = e`. Out: pointer `41 = M`
(one more than the least `k` with `b ≤ ρ k`), pointer `42 = t₀ = clog₂ (M - 1)`. Uses real regs
`41, 43`, pointers `40–43`. Exit: `off + 14`. -/
def ladder (off : ℕ) : Program :=
  [ .core (.pset 40 0),                 -- 0  k := 0
    .core (.sub 43 40 41),              -- 1  tmp := b - r
    .core (.jle 43 (off + 6)),          -- 2  b ≤ r → 6
    .core (.mul 41 41 42),              -- 3  r := r e
    .core (.pinc 40),                   -- 4  k := k + 1
    .core (.pjle 40 40 (off + 1)),      -- 5  → 1
    .core (.pcopy 41 40),               -- 6  M := k
    .core (.pinc 41),                   -- 7  M := k + 1
    .core (.pset 42 0),                 -- 8  t := 0
    .core (.pset 43 1),                 -- 9  w := 1
    .core (.pjle 40 43 (off + 14)),     -- 10 k ≤ w → exit
    .pointerAdd 43 43 43,               -- 11 w := 2 w
    .core (.pinc 42),                   -- 12 t := t + 1
    .core (.pjle 40 40 (off + 10)) ]    -- 13 → 10

/-- The search loop (`pc = off + 1`). -/
lemma ladder_loop (Q : Program) (off : ℕ) (hE : Embeds Q (ladder off) off) (ρ : ℕ → ℝ) (e b : ℝ)
    (hρ : ∀ k, ρ (k + 1) = ρ k * e) (K : ℕ) (hK : b ≤ ρ K) (hmin : ∀ k < K, ¬ b ≤ ρ k) :
    ∀ d j, j + d = K → ∀ s : State, s.core.pc = off + 1 → s.halted = false →
      s.core.regs 40 = b → s.core.regs 41 = ρ j → s.core.regs 42 = e → s.core.ptrs 40 = j →
      ∃ n, n = 5 * d + 2 ∧ (run Q s detTape n).core.pc = off + 6 ∧ (run Q s detTape n).halted = false ∧
        (run Q s detTape n).core.ptrs 40 = K ∧ (run Q s detTape n).core.mem = s.core.mem ∧
        (run Q s detTape n).integerMemory = s.integerMemory ∧
        (∀ x, x ≠ 40 → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 41 → x ≠ 43 → (run Q s detTape n).core.regs x = s.core.regs x) ∧
        (run Q s detTape n).work = s.work + n := by
  intro d
  induction d with
  | zero =>
    intro j hj s hpc hh h40 h41 h42 hp40
    simp only [Nat.add_zero] at hj; subst hj
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h40 h41 h42 hp40; subst hpc hh
    refine ⟨2, rfl, ?_⟩
    (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
    rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Function.update_apply]
    rw [if_pos (by simp [h40, h41]; exact hK), run_zero]
    refine ⟨rfl, rfl, hp40, rfl, rfl, fun x _ => rfl, ?_, by simp⟩
    intro x h1 h3; simp [Function.update_apply, h3]
  | succ d ih =>
    intro j hj s hpc hh h40 h41 h42 hp40
    have hlt : j < K := by omega
    have hno := hmin j hlt
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
    simp only at hpc hh h40 h41 h42 hp40; subst hpc hh
    set S := run Q ⟨⟨off + 1, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 5 with hSdef
    have hS : S.core.pc = off + 1 ∧ S.halted = false ∧ S.core.regs 40 = b ∧ S.core.regs 41 = ρ (j + 1) ∧
        S.core.regs 42 = e ∧ S.core.ptrs 40 = ((j + 1 : ℕ) : ℤ) ∧ S.core.mem = mem ∧ S.integerMemory = im ∧
        (∀ x, x ≠ 40 → S.core.ptrs x = ptrs x) ∧ (∀ x, x ≠ 41 → x ≠ 43 → S.core.regs x = regs x) ∧
        S.work = w + 5 := by
      rw [hSdef]
      (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
      rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Function.update_apply]
      rw [if_neg (by simp [h40, h41]; exact not_le.mp hno)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
      rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec]
      rw [if_pos le_rfl, run_zero]
      refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, ?_, rfl⟩
      · simp [Function.update_apply, h40]
      · simp [Function.update_apply, h41, h42, hρ]
      · simp [Function.update_apply, h42]
      · simp [Function.update_apply, hp40]
      · intro x hx; simp [Function.update_apply, hx]
      · intro x h1 h3; simp [Function.update_apply, h1, h3]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, aw⟩ := hS
    obtain ⟨n, hn, b1, b2, b3, b4, b5, b6, b7, bw⟩ := ih (j + 1) (by omega) S a1 a2 a3 a4 a5 a6
    refine ⟨5 + n, by omega, ?_⟩
    rw [run_add, ← hSdef]
    refine ⟨b1, b2, b3, by rw [b4, a7], by rw [b5, a8], ?_, ?_, by rw [bw, aw]; ring⟩
    · intro x hx; rw [b6 x hx, a9 x hx]
    · intro x h1 h3; rw [b7 x h1 h3, a10 x h1 h3]

/-- The `clog₂` loop (`pc = off + 10`). -/
lemma ladder_clog (Q : Program) (off : ℕ) (hE : Embeds Q (ladder off) off) (K : ℕ) :
    ∀ d t, t + d = Nat.clog 2 K → ∀ s : State, s.core.pc = off + 10 → s.halted = false →
      s.core.ptrs 40 = K → s.core.ptrs 42 = t → s.core.ptrs 43 = 2 ^ t →
      ∃ n, n = 4 * d + 1 ∧ (run Q s detTape n).core.pc = off + 14 ∧ (run Q s detTape n).halted = false ∧
        (run Q s detTape n).core.ptrs 42 = Nat.clog 2 K ∧ (run Q s detTape n).core.mem = s.core.mem ∧
        (run Q s detTape n).integerMemory = s.integerMemory ∧
        (∀ x, x ≠ 42 → x ≠ 43 → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape n).core.regs = s.core.regs ∧ (run Q s detTape n).work = s.work + n := by
  intro d
  induction d with
  | zero =>
    intro t ht s hpc hh h40 h42 h43
    simp only [Nat.add_zero] at ht; subst ht
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h40 h42 h43; subst hpc hh
    refine ⟨1, rfl, ?_⟩
    rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec]
    rw [if_pos (by rw [h40, h43]; exact_mod_cast Nat.le_pow_clog (by norm_num) K), run_zero]
    exact ⟨rfl, rfl, h42, rfl, rfl, fun _ _ _ => rfl, rfl, rfl⟩
  | succ d ih =>
    intro t ht s hpc hh h40 h42 h43
    have hlt : ¬ (K ≤ 2 ^ t) := by
      intro h; have := (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).2 h; omega
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt', w⟩ := s
    simp only at hpc hh h40 h42 h43; subst hpc hh
    set S := run Q ⟨⟨off + 10, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 4 with hSdef
    have hS : S.core.pc = off + 10 ∧ S.halted = false ∧ S.core.ptrs 40 = K ∧
        S.core.ptrs 42 = ((t + 1 : ℕ) : ℤ) ∧ S.core.ptrs 43 = 2 ^ (t + 1) ∧ S.core.mem = mem ∧
        S.integerMemory = im ∧ (∀ x, x ≠ 42 → x ≠ 43 → S.core.ptrs x = ptrs x) ∧
        S.core.regs = regs ∧ S.work = w + 4 := by
      rw [hSdef]
      rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec]
      rw [if_neg (by rw [h40, h43]; exact_mod_cast hlt)]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
      rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec]
      rw [if_pos le_rfl, run_zero]
      refine ⟨rfl, rfl, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl⟩
      · simp [Function.update_apply, h40]
      · simp [Function.update_apply, h42]
      · simp [Function.update_apply, h43]; ring
      · intro x h2 h3; simp [Function.update_apply, h2, h3]
    obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, aw⟩ := hS
    obtain ⟨n, hn, b1, b2, b3, b4, b5, b6, b7, bw⟩ := ih (t + 1) (by omega) S a1 a2 a3 a4 a5
    refine ⟨4 + n, by omega, ?_⟩
    rw [run_add, ← hSdef]
    refine ⟨b1, b2, b3, by rw [b4, a6], by rw [b5, a7], ?_, by rw [b7, a9], by rw [bw, aw]; ring⟩
    intro x h2 h3; rw [b6 x h2 h3, a8 x h2 h3]

/-- **Ladder block specification**, in any host `Q` embedding the block at `off`. -/
theorem ladder_spec (Q : Program) (off : ℕ) (hE : Embeds Q (ladder off) off) (ρ : ℕ → ℝ) (e b : ℝ)
    (hρ : ∀ k, ρ (k + 1) = ρ k * e) (hex : ∃ k, b ≤ ρ k) (s : State) (hpc : s.core.pc = off)
    (hh : s.halted = false) (h40 : s.core.regs 40 = b) (h41 : s.core.regs 41 = ρ 0)
    (h42 : s.core.regs 42 = e) :
    ∃ n, n = 5 * Nat.find hex + 4 * Nat.clog 2 (Nat.find hex) + 8 ∧
      (run Q s detTape n).core.pc = off + 14 ∧ (run Q s detTape n).halted = false ∧
      (run Q s detTape n).core.ptrs 41 = Nat.find hex + 1 ∧
      (run Q s detTape n).core.ptrs 42 = Nat.clog 2 (Nat.find hex) ∧
      (run Q s detTape n).core.mem = s.core.mem ∧ (run Q s detTape n).integerMemory = s.integerMemory ∧
      (∀ x, x ∉ [40, 41, 42, 43] → (run Q s detTape n).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 41 → x ≠ 43 → (run Q s detTape n).core.regs x = s.core.regs x) ∧
      (run Q s detTape n).work = s.work + n := by
  set K := Nat.find hex with hKdef
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh h40 h41 h42; subst pc hh
  -- step 0: k := 0
  set S0 := run Q ⟨⟨off, regs, ptrs, mem⟩, im, cur, false, w⟩ detTape 1 with hS0
  have e0 : S0 = ⟨⟨off + 1, regs, Function.update ptrs 40 0, mem⟩, im, cur, false, w + 1⟩ := by
    rw [hS0, run_exec_at (i := 0) hE rfl (by simp) rfl]; simp only [exec, coreExec]; rw [run_zero]
  obtain ⟨n1, hn1, a1, a2, a3, a4, a5, a6, a7, aw⟩ :=
    ladder_loop Q off hE ρ e b hρ K (Nat.find_spec hex) (fun k hk => Nat.find_min hex hk) K 0
      (by omega) S0 (by rw [e0]) (by rw [e0]) (by rw [e0]; exact h40) (by rw [e0]; exact h41)
      (by rw [e0]; exact h42) (by rw [e0]; simp)
  generalize hS1 : run Q S0 detTape n1 = S1 at a1 a2 a3 a4 a5 a6 a7 aw
  obtain ⟨⟨pc1, regs1, ptrs1, mem1⟩, im1, cur1, hlt1, w1⟩ := S1
  simp only at a1 a2 a3 a4 a5 a6 a7 aw; subst a1 a2
  -- steps 6–9
  set S2 := run Q ⟨⟨off + 6, regs1, ptrs1, mem1⟩, im1, cur1, false, w1⟩ detTape 4 with hS2
  have e2 : S2.core.pc = off + 10 ∧ S2.halted = false ∧ S2.core.ptrs 40 = K ∧ S2.core.ptrs 41 = K + 1 ∧
      S2.core.ptrs 42 = ((0 : ℕ) : ℤ) ∧ S2.core.ptrs 43 = 2 ^ 0 ∧ S2.core.mem = mem1 ∧
      S2.integerMemory = im1 ∧ (∀ x, x ∉ [41, 42, 43] → S2.core.ptrs x = ptrs1 x) ∧
      S2.core.regs = regs1 ∧ S2.work = w1 + 4 := by
    rw [hS2]; (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); rw [run_zero]
    refine ⟨rfl, rfl, ?_, ?_, ?_, ?_, rfl, rfl, ?_, rfl, rfl⟩
    · simp [Function.update_apply, a3]
    · simp [Function.update_apply, a3]
    · simp [Function.update_apply]
    · simp [Function.update_apply]
    · intro x hx; simp at hx; simp [Function.update_apply, hx]
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, cw⟩ := e2
  obtain ⟨n3, hn3, d1, d2, d3, d4, d5, d6, d7, dw⟩ :=
    ladder_clog Q off hE K (Nat.clog 2 K) 0 (by omega) S2 c1 c2 c3 c5 c6
  refine ⟨1 + n1 + 4 + n3, by omega, ?_⟩
  rw [run_add, run_add, run_add, ← hS0, hS1, ← hS2]
  refine ⟨d1, d2, ?_, d3, by rw [d4, c7, a4, e0], by rw [d5, c8, a5, e0], ?_, ?_, ?_⟩
  · rw [d6 41 (by norm_num) (by norm_num), c4]
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    rw [d6 x hx.2.2.1 hx.2.2.2, c9 x (by simp [hx.2.1, hx.2.2.1, hx.2.2.2]), a6 x hx.1, e0]
    simp [Function.update_apply, hx.1]
  · intro x h1 h3; rw [d7, c10, a7 x h1 h3, e0]
  · rw [dw, cw, aw, e0]; ring

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib DetANN.HPIM.QP

/-- Hosts are assembled as concatenations: a block sits at the length of what precedes it. -/
lemma embeds_append (A B C : Program) : Embeds (A ++ B ++ C) B A.length := by
  intro i x h
  have hi : i < B.length := (List.getElem?_eq_some_iff.1 h).1
  rw [List.append_assoc, List.getElem?_append_right (by omega), Nat.add_sub_cancel_left,
    List.getElem?_append_left hi]
  exact h

/-- Composition check: a toy host with the ladder at offset `2`, then `halt`. -/
example (ρ : ℕ → ℝ) (e b : ℝ) (hρ : ∀ k, ρ (k + 1) = ρ k * e) (hex : ∃ k, b ≤ ρ k) (s : State)
    (hpc : s.core.pc = 2) (hh : s.halted = false) (h40 : s.core.regs 40 = b)
    (h41 : s.core.regs 41 = ρ 0) (h42 : s.core.regs 42 = e) :
    ∃ n, (run ([.core (.pset 0 0), .core (.pset 1 0)] ++ ladder 2 ++ [.halt]) s detTape n).halted = true ∧
      (run ([.core (.pset 0 0), .core (.pset 1 0)] ++ ladder 2 ++ [.halt]) s detTape n).core.ptrs 41 =
        Nat.find hex + 1 := by
  obtain ⟨n, -, a1, a2, a3, -⟩ := ladder_spec _ 2
    (embeds_append [.core (.pset 0 0), .core (.pset 1 0)] (ladder 2) [.halt]) ρ e b hρ hex s hpc hh h40 h41 h42
  refine ⟨n + 1, ?_⟩
  rw [run_add, run_exec a2 (by rw [a1]; rfl)]
  simp only [exec, run_zero]
  exact ⟨trivial, a3⟩

end DetANN.HPIM.PP

-- ===== PP_Prog =====
/-! The preprocessing program `P`: driver segments and assembly over the child blocks. -/

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth

-- Generated by notes/lemma33/p_gen.py from p_driver.py. Do not edit by hand.

/-- Driver segment 0 (39 instructions). Labels: CL = off + 14, CLE = off + 18, PAL = off + 26, PAE = off + 32. -/
def seg0 (off : ℕ) : Program :=
  [ .core (.pset 6 (0)),
    .integerLoad 23 6,
    .core (.pset 6 (1)),
    .integerLoad 1 6,
    .core (.pset 6 (0)),
    .core (.load 0 6),
    .core (.const 20 (0 : ℝ)),
    .core (.const 21 (2 : ℝ)),
    .core (.const 22 (4 : ℝ)),
    .core (.div 6 0 22),
    .core (.const 7 (1 : ℝ)),
    .core (.add 1 7 6),
    .core (.pset 5 (0)),
    .core (.pset 6 (1)),
    .core (.pjle 23 6 (off + 18)),
    .pointerAdd 6 6 6,
    .core (.pinc 5),
    .core (.pjle 0 0 (off + 14)),
    .pointerReal 5 5,
    .core (.add 5 5 7),
    .core (.mul 5 22 5),
    .core (.div 2 5 0),
    .core (.pset 12 (4)),
    .core (.pset 6 (1)),
    .core (.pset 3 (0)),
    .core (.pcopy 7 12),
    .core (.pjle 23 3 (off + 32)),
    .integerStore 7 6,
    .pointerAdd 6 6 1,
    .core (.pinc 7),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 26)),
    .core (.pcopy 16 6),
    .core (.const 5 (8 : ℝ)),
    .pointerReal 6 23,
    .core (.mul 40 5 6),
    .core (.mul 40 40 2),
    .core (.div 41 7 1),
    .core (.add 42 1 20) ]

/-- Driver segment 2 (58 instructions). Labels: PWL = off + 6, PWB = off + 8, PWE = off + 13, RSL = off + 17, RSE = off + 22, NODE = off + 39, INNER = off + 54. -/
def seg2 (off RETURN : ℕ) : Program :=
  [ .pointerAdd 9 12 23,
    .core (.pset 6 (3)),
    .integerStore 6 9,
    .core (.pset 3 (0)),
    .core (.pset 6 (1)),
    .core (.pcopy 7 9),
    .core (.pjle 3 42 (off + 8)),
    .core (.pjle 0 0 (off + 13)),
    .integerStore 7 6,
    .pointerAdd 6 6 6,
    .core (.pinc 7),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 6)),
    .core (.pcopy 15 7),
    .core (.pcopy 10 15),
    .core (.pset 3 (0)),
    .core (.pcopy 7 10),
    .core (.pjle 23 3 (off + 22)),
    .integerStore 7 3,
    .core (.pinc 7),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 17)),
    .core (.pcopy 2 7),
    .core (.pset 27 (3)),
    .pointerAdd 6 2 27,
    .integerStore 6 10,
    .core (.pset 27 (7)),
    .pointerAdd 6 2 27,
    .integerStore 6 23,
    .core (.pset 27 (8)),
    .pointerAdd 15 2 27,
    .core (.pset 6 (2)),
    .integerStore 6 2,
    .core (.pset 8 (-10)),
    .core (.pset 6 (0)),
    .integerStore 8 6,
    .core (.pcopy 13 8),
    .core (.pset 14 (0)),
    .core (.pjle 0 0 (off + 39)),
    .core (.pset 27 (3)),
    .pointerAdd 6 2 27,
    .integerLoad 10 6,
    .core (.pset 27 (7)),
    .pointerAdd 6 2 27,
    .integerLoad 11 6,
    .core (.pset 27 (2)),
    .core (.pjle 27 11 (off + 54)),
    .core (.pset 6 (0)),
    .integerStore 2 6,
    .integerLoad 6 10,
    .core (.pcopy 7 2),
    .core (.pinc 7),
    .integerStore 7 6,
    .core (.pjle 0 0 (RETURN)),
    .core (.pset 6 (1)),
    .integerStore 2 6,
    .core (.pcopy 20 13),
    .core (.pcopy 28 14) ]

/-- Driver segment 4 (9 instructions). Labels: . -/
def seg4 (off : ℕ) : Program :=
  [ .core (.div 3 10 21),
    .pointerReal 6 11,
    .core (.mul 40 21 6),
    .core (.mul 40 40 2),
    .core (.mul 40 40 3),
    .core (.div 41 3 21),
    .core (.div 41 41 21),
    .core (.div 41 41 1),
    .core (.add 42 1 20) ]

/-- Driver segment 6 (82 instructions). Labels: LK = off + 22, B1 = off + 25, B2 = off + 33, SMN = off + 43, CMX = off + 44, SMX = off + 47, NX = off + 48, B2E = off + 50, SGS = off + 60, SGN = off + 61, B1E = off + 63, B3 = off + 66, B3E = off + 77. -/
def seg6 (off LKE : ℕ) : Program :=
  [ .core (.pcopy 4 41),
    .core (.pcopy 5 42),
    .core (.pcopy 6 2),
    .core (.pinc 6),
    .integerStore 6 4,
    .core (.pset 27 (6)),
    .pointerAdd 6 2 27,
    .integerStore 6 5,
    .core (.pcopy 18 15),
    .pointerAdd 15 15 4,
    .core (.pset 27 (2)),
    .pointerAdd 6 2 27,
    .integerStore 6 18,
    .core (.pcopy 19 15),
    .pointerAdd 15 15 11,
    .core (.pset 27 (4)),
    .pointerAdd 6 2 27,
    .integerStore 6 19,
    .core (.div 4 3 21),
    .core (.div 4 4 21),
    .core (.div 4 4 1),
    .core (.pset 3 (0)),
    .core (.pjle 4 3 (LKE)),
    .core (.pcopy 29 16),
    .core (.pset 22 (0)),
    .core (.pjle 1 22 (off + 63)),
    .integerLoad 6 10,
    .pointerAdd 6 12 6,
    .integerLoad 6 6,
    .pointerAdd 6 6 22,
    .core (.load 15 6),
    .core (.add 16 15 20),
    .core (.pset 31 (1)),
    .core (.pjle 11 31 (off + 50)),
    .pointerAdd 6 10 31,
    .integerLoad 6 6,
    .pointerAdd 6 12 6,
    .integerLoad 6 6,
    .pointerAdd 6 6 22,
    .core (.load 17 6),
    .core (.sub 5 17 15),
    .core (.jle 5 (off + 43)),
    .core (.pjle 0 0 (off + 44)),
    .core (.add 15 17 20),
    .core (.sub 5 16 17),
    .core (.jle 5 (off + 47)),
    .core (.pjle 0 0 (off + 48)),
    .core (.add 16 17 20),
    .core (.pinc 31),
    .core (.pjle 0 0 (off + 33)),
    .pointerAdd 6 29 22,
    .core (.store 6 15),
    .pointerAdd 6 6 1,
    .core (.store 6 16),
    .core (.sub 5 16 15),
    .core (.pset 27 (0)),
    .core (.pjle 22 27 (off + 60)),
    .core (.sub 6 13 5),
    .core (.jle 6 (off + 60)),
    .core (.pjle 0 0 (off + 61)),
    .core (.add 13 5 20),
    .core (.pinc 22),
    .core (.pjle 0 0 (off + 25)),
    .core (.mul 14 22 4),
    .core (.add 14 13 14),
    .core (.pset 22 (0)),
    .core (.pjle 1 22 (off + 77)),
    .pointerAdd 6 29 22,
    .core (.load 15 6),
    .core (.sub 15 15 14),
    .core (.store 6 15),
    .pointerAdd 6 6 1,
    .core (.load 16 6),
    .core (.add 16 16 14),
    .core (.store 6 16),
    .core (.pinc 22),
    .core (.pjle 0 0 (off + 66)),
    .pointerAdd 16 16 1,
    .pointerAdd 16 16 1,
    .core (.pcopy 17 29),
    .core (.add 11 4 20),
    .core (.add 12 1 20) ]

/-- Driver segment 8 (0 instructions). Labels: . -/
def seg8 (off : ℕ) : Program :=
  [  ]

/-- Driver segment 10 (26 instructions). Labels: LKE = off + 25. -/
def seg10 (off LK : ℕ) : Program :=
  [ .core (.pset 6 (1)),
    .integerStore 15 6,
    .core (.pcopy 7 15),
    .core (.pinc 7),
    .integerStore 7 29,
    .core (.pinc 7),
    .integerStore 7 17,
    .core (.pinc 7),
    .core (.pcopy 6 15),
    .core (.pset 27 (4)),
    .pointerAdd 6 6 27,
    .integerStore 7 6,
    .core (.pset 0 (0)),
    .integerStore 6 0,
    .core (.pinc 6),
    .integerStore 6 0,
    .pointerAdd 6 18 3,
    .integerStore 6 15,
    .core (.pset 27 (6)),
    .pointerAdd 15 15 27,
    .core (.pcopy 13 20),
    .core (.pcopy 14 28),
    .core (.mul 4 4 1),
    .core (.pinc 3),
    .core (.pjle 0 0 (LK)),
    .core (.mul 10 21 3) ]

/-- Driver segment 12 (29 instructions). Labels: RL = off + 3, RT = off + 9, RN = off + 14, RE = off + 16. -/
def seg12 (off : ℕ) : Program :=
  [ .core (.pcopy 25 15),
    .core (.pset 24 (0)),
    .core (.pset 3 (0)),
    .core (.pjle 11 3 (off + 16)),
    .pointerSub 6 20 3,
    .core (.pdec 6),
    .integerLoad 30 6,
    .core (.pjle 3 30 (off + 9)),
    .core (.pjle 0 0 (off + 14)),
    .pointerAdd 6 10 3,
    .integerLoad 7 6,
    .pointerAdd 6 25 24,
    .integerStore 6 7,
    .core (.pinc 24),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 3)),
    .pointerAdd 21 25 24,
    .core (.pset 27 (3)),
    .pointerAdd 6 21 27,
    .integerStore 6 25,
    .core (.pset 27 (7)),
    .pointerAdd 6 21 27,
    .integerStore 6 24,
    .core (.pset 27 (8)),
    .pointerAdd 15 21 27,
    .core (.pset 27 (5)),
    .pointerAdd 6 2 27,
    .integerStore 6 21,
    .core (.add 10 3 20) ]

/-- Driver segment 14 (107 instructions). Labels: KL = off + 1, KNEW = off + 7, K1 = off + 10, K1A = off + 16, K1T = off + 18, K1N = off + 23, K1E = off + 25, K2 = off + 35, K2A = off + 41, K2T = off + 43, K2N = off + 45, K2E = off + 47, KN = off + 76, KE = off + 78, RETURN = off + 82, HALT = off + 106. -/
def seg14 (off NODE : ℕ) : Program :=
  [ .core (.pset 3 (0)),
    .core (.pjle 11 3 (off + 78)),
    .pointerSub 6 20 3,
    .core (.pdec 6),
    .integerLoad 30 6,
    .core (.pjle 3 30 (off + 7)),
    .core (.pjle 0 0 (off + 76)),
    .core (.pcopy 25 15),
    .core (.pset 24 (0)),
    .core (.pcopy 22 3),
    .core (.pjle 11 22 (off + 25)),
    .pointerSub 6 20 22,
    .core (.pdec 6),
    .integerLoad 31 6,
    .core (.pjle 31 3 (off + 16)),
    .core (.pjle 0 0 (off + 23)),
    .core (.pjle 3 31 (off + 18)),
    .core (.pjle 0 0 (off + 23)),
    .pointerAdd 6 10 22,
    .integerLoad 7 6,
    .pointerAdd 6 25 24,
    .integerStore 6 7,
    .core (.pinc 24),
    .core (.pinc 22),
    .core (.pjle 0 0 (off + 10)),
    .pointerAdd 26 25 24,
    .core (.pset 27 (3)),
    .pointerAdd 6 26 27,
    .integerStore 6 25,
    .core (.pset 27 (7)),
    .pointerAdd 6 26 27,
    .integerStore 6 24,
    .core (.pset 27 (8)),
    .pointerAdd 15 26 27,
    .core (.pcopy 22 3),
    .core (.pjle 11 22 (off + 47)),
    .pointerSub 6 20 22,
    .core (.pdec 6),
    .integerLoad 31 6,
    .core (.pjle 31 3 (off + 41)),
    .core (.pjle 0 0 (off + 45)),
    .core (.pjle 3 31 (off + 43)),
    .core (.pjle 0 0 (off + 45)),
    .pointerAdd 6 19 22,
    .integerStore 6 26,
    .core (.pinc 22),
    .core (.pjle 0 0 (off + 35)),
    .pointerSub 6 20 11,
    .core (.pset 27 (10)),
    .pointerSub 6 6 27,
    .core (.pset 7 (1)),
    .core (.pcopy 9 6),
    .integerStore 9 7,
    .core (.pinc 9),
    .integerStore 9 2,
    .core (.pinc 9),
    .integerStore 9 3,
    .core (.pinc 9),
    .integerStore 9 11,
    .core (.pinc 9),
    .integerStore 9 10,
    .core (.pinc 9),
    .integerStore 9 20,
    .core (.pinc 9),
    .integerStore 9 19,
    .core (.pinc 9),
    .integerStore 9 21,
    .core (.pinc 9),
    .integerStore 9 8,
    .core (.pinc 9),
    .integerStore 9 28,
    .core (.pcopy 8 6),
    .core (.pcopy 13 6),
    .core (.pcopy 14 28),
    .core (.pcopy 2 26),
    .core (.pjle 0 0 (NODE)),
    .core (.pinc 3),
    .core (.pjle 0 0 (off + 1)),
    .core (.pcopy 2 21),
    .core (.pcopy 13 20),
    .core (.pcopy 14 28),
    .core (.pjle 0 0 (NODE)),
    .integerLoad 6 8,
    .core (.pset 27 (0)),
    .core (.pjle 6 27 (off + 106)),
    .core (.pcopy 9 8),
    .core (.pinc 9),
    .integerLoad 2 9,
    .core (.pinc 9),
    .integerLoad 3 9,
    .core (.pinc 9),
    .integerLoad 11 9,
    .core (.pinc 9),
    .integerLoad 10 9,
    .core (.pinc 9),
    .integerLoad 20 9,
    .core (.pinc 9),
    .integerLoad 19 9,
    .core (.pinc 9),
    .integerLoad 21 9,
    .core (.pinc 9),
    .core (.pinc 9),
    .integerLoad 28 9,
    .core (.pdec 9),
    .integerLoad 8 9,
    .core (.pjle 0 0 (off + 76)),
    .halt ]

/-- The child blocks and their lengths. -/
structure Blocks where
  med : ℕ → Program
  comps : ℕ → Program
  build : ℕ → Program
  bal : ℕ → Program
  Lm : ℕ
  Lc : ℕ
  Lb : ℕ
  Lbal : ℕ

namespace Blocks

/-- Offset of piece 0. -/
def o0 (B : Blocks) : ℕ := 0
/-- Offset of piece 1. -/
def o1 (B : Blocks) : ℕ := 39
/-- Offset of piece 2. -/
def o2 (B : Blocks) : ℕ := 39 + 14
/-- Offset of piece 3. -/
def o3 (B : Blocks) : ℕ := 39 + 14 + 58
/-- Offset of piece 4. -/
def o4 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm
/-- Offset of piece 5. -/
def o5 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9
/-- Offset of piece 6. -/
def o6 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14
/-- Offset of piece 7. -/
def o7 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82
/-- Offset of piece 8. -/
def o8 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb
/-- Offset of piece 9. -/
def o9 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0
/-- Offset of piece 10. -/
def o10 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal
/-- Offset of piece 11. -/
def o11 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26
/-- Offset of piece 12. -/
def o12 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc
/-- Offset of piece 13. -/
def o13 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc + 29
/-- Offset of piece 14. -/
def o14 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm + 9 + 14 + 82 + B.Lb + 0 + B.Lbal + 26 + B.Lc + 29 + B.Lc
def lbl_CL (B : Blocks) : ℕ := B.o0 + 14
def lbl_CLE (B : Blocks) : ℕ := B.o0 + 18
def lbl_PAL (B : Blocks) : ℕ := B.o0 + 26
def lbl_PAE (B : Blocks) : ℕ := B.o0 + 32
def lbl_PWL (B : Blocks) : ℕ := B.o2 + 6
def lbl_PWB (B : Blocks) : ℕ := B.o2 + 8
def lbl_PWE (B : Blocks) : ℕ := B.o2 + 13
def lbl_RSL (B : Blocks) : ℕ := B.o2 + 17
def lbl_RSE (B : Blocks) : ℕ := B.o2 + 22
def lbl_NODE (B : Blocks) : ℕ := B.o2 + 39
def lbl_INNER (B : Blocks) : ℕ := B.o2 + 54
def lbl_LK (B : Blocks) : ℕ := B.o6 + 22
def lbl_B1 (B : Blocks) : ℕ := B.o6 + 25
def lbl_B2 (B : Blocks) : ℕ := B.o6 + 33
def lbl_SMN (B : Blocks) : ℕ := B.o6 + 43
def lbl_CMX (B : Blocks) : ℕ := B.o6 + 44
def lbl_SMX (B : Blocks) : ℕ := B.o6 + 47
def lbl_NX (B : Blocks) : ℕ := B.o6 + 48
def lbl_B2E (B : Blocks) : ℕ := B.o6 + 50
def lbl_SGS (B : Blocks) : ℕ := B.o6 + 60
def lbl_SGN (B : Blocks) : ℕ := B.o6 + 61
def lbl_B1E (B : Blocks) : ℕ := B.o6 + 63
def lbl_B3 (B : Blocks) : ℕ := B.o6 + 66
def lbl_B3E (B : Blocks) : ℕ := B.o6 + 77
def lbl_LKE (B : Blocks) : ℕ := B.o10 + 25
def lbl_RL (B : Blocks) : ℕ := B.o12 + 3
def lbl_RT (B : Blocks) : ℕ := B.o12 + 9
def lbl_RN (B : Blocks) : ℕ := B.o12 + 14
def lbl_RE (B : Blocks) : ℕ := B.o12 + 16
def lbl_KL (B : Blocks) : ℕ := B.o14 + 1
def lbl_KNEW (B : Blocks) : ℕ := B.o14 + 7
def lbl_K1 (B : Blocks) : ℕ := B.o14 + 10
def lbl_K1A (B : Blocks) : ℕ := B.o14 + 16
def lbl_K1T (B : Blocks) : ℕ := B.o14 + 18
def lbl_K1N (B : Blocks) : ℕ := B.o14 + 23
def lbl_K1E (B : Blocks) : ℕ := B.o14 + 25
def lbl_K2 (B : Blocks) : ℕ := B.o14 + 35
def lbl_K2A (B : Blocks) : ℕ := B.o14 + 41
def lbl_K2T (B : Blocks) : ℕ := B.o14 + 43
def lbl_K2N (B : Blocks) : ℕ := B.o14 + 45
def lbl_K2E (B : Blocks) : ℕ := B.o14 + 47
def lbl_KN (B : Blocks) : ℕ := B.o14 + 76
def lbl_KE (B : Blocks) : ℕ := B.o14 + 78
def lbl_RETURN (B : Blocks) : ℕ := B.o14 + 82
def lbl_HALT (B : Blocks) : ℕ := B.o14 + 106

/-- The preprocessing program. -/
def prog (B : Blocks) : Program :=
  seg0 B.o0 ++
  ladder B.o1 ++
  seg2 B.o2 B.lbl_RETURN ++
  B.med B.o3 ++
  seg4 B.o4 ++
  ladder B.o5 ++
  seg6 B.o6 B.lbl_LKE ++
  B.build B.o7 ++
  seg8 B.o8 ++
  B.bal B.o9 ++
  seg10 B.o10 B.lbl_LK ++
  B.comps B.o11 ++
  seg12 B.o12 ++
  B.comps B.o13 ++
  seg14 B.o14 B.lbl_NODE

end Blocks

end DetANN.HPIM.PP

-- ===== PP_Basic =====
/-! Infrastructure for the preprocessing program: unchanged cells, `cellsWritten` over run
segments, and the embedding of every piece in `prog B`. -/

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN

/-- One step changes real cell `z` only if it stores to it. -/
lemma step_mem (P : Program) (ω : ℕ → Bool) (s : State) (z : ℤ)
    (h : writtenCell P s ≠ some (true, z)) : (step P ω s).core.mem z = s.core.mem z := by
  unfold writtenCell at h
  by_cases hh : s.halted = true
  · simp [step, hh]
  · simp only [Bool.not_eq_true] at hh
    rcases hP : P[s.core.pc]? with _ | ins
    · simp [step, hh, hP]
    · rw [step_eq_exec P ω s ins hh hP]
      simp only [hh, hP] at h
      cases ins with
      | core i =>
        cases i <;> simp only [exec, coreExec] <;> try rfl
        case store q r =>
          simp only [Bool.false_eq_true, if_false, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and] at h
          rw [Function.update_of_ne (Ne.symm h)]
        all_goals (split_ifs <;> rfl)
      | _ => simp [exec]

/-- One step changes integer cell `z` only if it stores to it. -/
lemma step_im (P : Program) (ω : ℕ → Bool) (s : State) (z : ℤ)
    (h : writtenCell P s ≠ some (false, z)) : (step P ω s).integerMemory z = s.integerMemory z := by
  unfold writtenCell at h
  by_cases hh : s.halted = true
  · simp [step, hh]
  · simp only [Bool.not_eq_true] at hh
    rcases hP : P[s.core.pc]? with _ | ins
    · simp [step, hh, hP]
    · rw [step_eq_exec P ω s ins hh hP]
      simp only [hh, hP] at h
      cases ins with
      | integerStore a b =>
        simp only [Bool.false_eq_true, if_false, ne_eq, Option.some.injEq, Prod.mk.injEq, true_and] at h
        simp only [exec]; rw [Function.update_of_ne (Ne.symm h)]
      | core i => simp [exec]
      | _ => simp [exec]

lemma run_succ' (P : Program) (s : State) (ω : ℕ → Bool) (t : ℕ) :
    run P s ω (t + 1) = step P ω (run P s ω t) := by
  rw [run_add, run_succ, run_zero]

/-- `cellsWritten` over consecutive run segments. -/
lemma cellsWritten_add (P : Program) (s : State) (a b : ℕ) :
    cellsWritten P s (a + b) = cellsWritten P s a ∪ cellsWritten P (run P s detTape a) b := by
  ext c
  simp only [cellsWritten, Finset.mem_union, Finset.mem_biUnion, Finset.mem_range]
  constructor
  · rintro ⟨i, hi, hc⟩
    by_cases hia : i < a
    · exact Or.inl ⟨i, hia, hc⟩
    · refine Or.inr ⟨i - a, by omega, ?_⟩
      rw [← run_add, Nat.add_sub_cancel' (by omega)]; exact hc
  · rintro (⟨i, hi, hc⟩ | ⟨i, hi, hc⟩)
    · exact ⟨i, by omega, hc⟩
    · exact ⟨a + i, by omega, by rw [run_add]; exact hc⟩

lemma cellsWritten_zero (P : Program) (s : State) : cellsWritten P s 0 = ∅ := by
  simp [cellsWritten]

/-- A real cell that is never written keeps its value. -/
lemma run_mem_unwritten (P : Program) (s : State) (z : ℤ) :
    ∀ t, (true, z) ∉ cellsWritten P s t → (run P s detTape t).core.mem z = s.core.mem z := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    rw [cellsWritten_add] at h
    simp only [Finset.mem_union, not_or] at h
    rw [run_succ', step_mem]
    · exact ih h.1
    · intro h'; apply h.2
      simp [cellsWritten, run_zero, h']

/-- An integer cell that is never written keeps its value. -/
lemma run_im_unwritten (P : Program) (s : State) (z : ℤ) :
    ∀ t, (false, z) ∉ cellsWritten P s t →
      (run P s detTape t).integerMemory z = s.integerMemory z := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    rw [cellsWritten_add] at h
    simp only [Finset.mem_union, not_or] at h
    rw [run_succ', step_im]
    · exact ih h.1
    · intro h'; apply h.2
      simp [cellsWritten, run_zero, h']

/-- Cells outside a write window keep their values. -/
lemma unwritten_of_writesOnly {P : Program} {s : State} {t : ℕ} {W : Bool × ℤ → Prop}
    (h : WritesOnly P s t W) :
    (∀ z, ¬ W (true, z) → (run P s detTape t).core.mem z = s.core.mem z) ∧
    (∀ z, ¬ W (false, z) → (run P s detTape t).integerMemory z = s.integerMemory z) :=
  ⟨fun z hz => run_mem_unwritten P s z t (fun hc => hz (h _ hc)),
   fun z hz => run_im_unwritten P s z t (fun hc => hz (h _ hc))⟩

/-! ### Embedding of the pieces -/

lemma embeds_append_right {A B : Program} {off : ℕ} (C : Program) (h : Embeds A B off) :
    Embeds (A ++ C) B off := by
  intro i x hx
  have := h i x hx
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 this).1]
  exact this

lemma embeds_tail (X p : Program) : Embeds (X ++ p) p X.length := by
  intro i x h
  rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left]
  exact h

/-- The child blocks have their declared lengths. -/
def Blocks.WF (B : Blocks) : Prop :=
  (∀ off, (B.med off).length = B.Lm) ∧ (∀ off, (B.comps off).length = B.Lc) ∧
    (∀ off, (B.build off).length = B.Lb) ∧ (∀ off, (B.bal off).length = B.Lbal)

lemma ladder_len (off : ℕ) : (ladder off).length = 14 := rfl

lemma seg0_len (off : ℕ) : (seg0 off).length = 39 := rfl
lemma seg2_len (off RETURN : ℕ) : (seg2 off RETURN).length = 58 := rfl
lemma seg4_len (off : ℕ) : (seg4 off).length = 9 := rfl
lemma seg6_len (off LKE : ℕ) : (seg6 off LKE).length = 82 := rfl
lemma seg8_len (off : ℕ) : (seg8 off).length = 0 := rfl
lemma seg10_len (off LK : ℕ) : (seg10 off LK).length = 26 := rfl
lemma seg12_len (off : ℕ) : (seg12 off).length = 29 := rfl
lemma seg14_len (off NODE : ℕ) : (seg14 off NODE).length = 107 := rfl

variable (B : Blocks)

lemma emb0 (hB : B.WF) : Embeds (Blocks.prog B) (seg0 B.o0) (B.o0) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 14 apply embeds_append_right
  have := embeds_tail ([]) (seg0 B.o0)
  convert this using 1
  all_goals first | rfl | simp [Blocks.o0]

lemma emb1 (hB : B.WF) : Embeds (Blocks.prog B) (ladder B.o1) (B.o1) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 13 apply embeds_append_right
  have := embeds_tail (seg0 B.o0) (ladder B.o1)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb2 (hB : B.WF) : Embeds (Blocks.prog B) (seg2 B.o2 B.lbl_RETURN) (B.o2) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 12 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1) (seg2 B.o2 B.lbl_RETURN)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb3 (hB : B.WF) : Embeds (Blocks.prog B) (B.med B.o3) (B.o3) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 11 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN) (B.med B.o3)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb4 (hB : B.WF) : Embeds (Blocks.prog B) (seg4 B.o4) (B.o4) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 10 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3) (seg4 B.o4)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb5 (hB : B.WF) : Embeds (Blocks.prog B) (ladder B.o5) (B.o5) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 9 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4) (ladder B.o5)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb6 (hB : B.WF) : Embeds (Blocks.prog B) (seg6 B.o6 B.lbl_LKE) (B.o6) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 8 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5) (seg6 B.o6 B.lbl_LKE)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb7 (hB : B.WF) : Embeds (Blocks.prog B) (B.build B.o7) (B.o7) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 7 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE) (B.build B.o7)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb8 (hB : B.WF) : Embeds (Blocks.prog B) (seg8 B.o8) (B.o8) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 6 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7) (seg8 B.o8)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb9 (hB : B.WF) : Embeds (Blocks.prog B) (B.bal B.o9) (B.o9) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 5 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8) (B.bal B.o9)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb10 (hB : B.WF) : Embeds (Blocks.prog B) (seg10 B.o10 B.lbl_LK) (B.o10) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 4 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9) (seg10 B.o10 B.lbl_LK)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb11 (hB : B.WF) : Embeds (Blocks.prog B) (B.comps B.o11) (B.o11) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 3 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9 ++ seg10 B.o10 B.lbl_LK) (B.comps B.o11)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb12 (hB : B.WF) : Embeds (Blocks.prog B) (seg12 B.o12) (B.o12) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 2 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9 ++ seg10 B.o10 B.lbl_LK ++ B.comps B.o11) (seg12 B.o12)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb13 (hB : B.WF) : Embeds (Blocks.prog B) (B.comps B.o13) (B.o13) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  iterate 1 apply embeds_append_right
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9 ++ seg10 B.o10 B.lbl_LK ++ B.comps B.o11 ++ seg12 B.o12) (B.comps B.o13)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

lemma emb14 (hB : B.WF) : Embeds (Blocks.prog B) (seg14 B.o14 B.lbl_NODE) (B.o14) := by
  obtain ⟨h1, h2, h3, h4⟩ := hB
  unfold Blocks.prog
  skip
  have := embeds_tail (seg0 B.o0 ++ ladder B.o1 ++ seg2 B.o2 B.lbl_RETURN ++ B.med B.o3 ++ seg4 B.o4 ++ ladder B.o5 ++ seg6 B.o6 B.lbl_LKE ++ B.build B.o7 ++ seg8 B.o8 ++ B.bal B.o9 ++ seg10 B.o10 B.lbl_LK ++ B.comps B.o11 ++ seg12 B.o12 ++ B.comps B.o13) (seg14 B.o14 B.lbl_NODE)
  convert this using 1
  simp only [List.length_append, List.length_nil, seg0_len, seg2_len, seg4_len, seg6_len, seg8_len, seg10_len, seg12_len, seg14_len, ladder_len, h1, h2, h3, h4]; rfl

end DetANN.HPIM.PP

-- ===== PP_Det =====
/-! The preprocessing program is deterministic and admissible. -/

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib DetANN DetANN.HPIM

/-- One admissible deterministic instruction. -/
def Good (op : Instr) : Prop :=
  (match op with
    | .core (.const _ value) => ∃ q : ℚ, value = (q : ℝ)
    | .core .accept | .core .reject => False
    | _ => True) ∧ (∀ r, op ≠ .coin r) ∧ (∀ r a e, op ≠ .rpow r a e)

lemma det_of_good {P : Program} (h : ∀ op ∈ P, Good op) : DetProgram P :=
  ⟨fun op hop => (h op hop).1, fun op hop => (h op hop).2⟩

lemma det_append {A B : Program} (hA : DetProgram A) (hB : DetProgram B) : DetProgram (A ++ B) := by
  refine ⟨fun op hop => ?_, fun op hop => ?_⟩
  · rcases List.mem_append.1 hop with h | h
    · exact hA.1 op h
    · exact hB.1 op h
  · rcases List.mem_append.1 hop with h | h
    · exact hA.2 op h
    · exact hB.2 op h

lemma det_seg0 (off : ℕ) : DetProgram (seg0 off) := by
  apply det_of_good
  intro op hop
  unfold seg0 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_ladder (off : ℕ) : DetProgram (ladder off) := by
  apply det_of_good
  intro op hop
  unfold ladder at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg2 (off R : ℕ) : DetProgram (seg2 off R) := by
  apply det_of_good
  intro op hop
  unfold seg2 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg4 (off : ℕ) : DetProgram (seg4 off) := by
  apply det_of_good
  intro op hop
  unfold seg4 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg6 (off R : ℕ) : DetProgram (seg6 off R) := by
  apply det_of_good
  intro op hop
  unfold seg6 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg8 (off : ℕ) : DetProgram (seg8 off) := by
  apply det_of_good
  intro op hop
  unfold seg8 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg10 (off R : ℕ) : DetProgram (seg10 off R) := by
  apply det_of_good
  intro op hop
  unfold seg10 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg12 (off : ℕ) : DetProgram (seg12 off) := by
  apply det_of_good
  intro op hop
  unfold seg12 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

lemma det_seg14 (off R : ℕ) : DetProgram (seg14 off R) := by
  apply det_of_good
  intro op hop
  unfold seg14 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done) | (refine ⟨1, ?_⟩; norm_num; done)
    | (refine ⟨2, ?_⟩; norm_num; done) | (refine ⟨4, ?_⟩; norm_num; done)
    | (refine ⟨8, ?_⟩; norm_num; done)

theorem det_prog (B : Blocks) (h1 : ∀ off, DetProgram (B.med off)) (h2 : ∀ off, DetProgram (B.comps off))
    (h3 : ∀ off, DetProgram (B.build off)) (h4 : ∀ off, DetProgram (B.bal off)) :
    DetProgram (Blocks.prog B) := by
  unfold Blocks.prog
  repeat' apply det_append
  all_goals first
    | exact det_seg0 _ | exact det_ladder _ | exact det_seg2 _ _ | exact det_seg4 _
    | exact det_seg6 _ _ | exact det_seg8 _ | exact det_seg10 _ _ | exact det_seg12 _
    | exact det_seg14 _ _ | exact h1 _ | exact h2 _ | exact h3 _ | exact h4 _

end DetANN.HPIM.PP

-- ===== PP_Sem =====
/-! Semantic facts used by the driver: component minima, sorted index lists, the radius ladder. -/

namespace DetANN.HPIM.PP

open DetANN.HPIM

variable {m : ℕ}

section Comp

variable {n : ℕ} (P : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ)

lemma thrReach_refl (i : Fin n) : thrReach P d i i := SimpleGraph.Reachable.refl _
lemma thrReach_symm {i j : Fin n} (h : thrReach P d i j) : thrReach P d j i :=
  SimpleGraph.Reachable.symm h
lemma thrReach_trans {i j k : Fin n} (h : thrReach P d i j) (h' : thrReach P d j k) :
    thrReach P d i k := SimpleGraph.Reachable.trans h h'

open Classical in
/-- The component of `i`, as a finset of local indices. -/
noncomputable def compSet (i : Fin n) : Finset (Fin n) := Finset.univ.filter (thrReach P d i)

lemma mem_compSet {i j : Fin n} : j ∈ compSet P d i ↔ thrReach P d i j := by
  classical
  simp [compSet]

lemma compSet_eq {i j : Fin n} (h : thrReach P d i j) : compSet P d i = compSet P d j := by
  ext k; rw [mem_compSet, mem_compSet]
  exact ⟨fun h' => thrReach_trans P d (thrReach_symm P d h) h', fun h' => thrReach_trans P d h h'⟩

lemma compMin_eq_min' (i : Fin n) :
    compMin P d i = ((compSet P d i).min' ⟨i, (mem_compSet P d).2 (thrReach_refl P d i)⟩ : ℕ) := by
  classical
  unfold compMin compSet
  rfl

lemma compMin_lt (i : Fin n) : compMin P d i < n := by
  rw [compMin_eq_min']; exact Fin.isLt _

/-- The component minimum as a local index. -/
noncomputable def compMinF (i : Fin n) : Fin n := ⟨compMin P d i, compMin_lt P d i⟩

lemma compMinF_mem (i : Fin n) : compMinF P d i ∈ compSet P d i := by
  have h := Finset.min'_mem (compSet P d i) ⟨i, (mem_compSet P d).2 (thrReach_refl P d i)⟩
  convert h using 1
  ext; simp [compMinF, compMin_eq_min']

lemma compMin_le (i : Fin n) : compMin P d i ≤ i := by
  rw [compMin_eq_min']
  exact_mod_cast Finset.min'_le _ _ ((mem_compSet P d).2 (thrReach_refl P d i))

lemma reach_compMin (i : Fin n) : thrReach P d i (compMinF P d i) :=
  (mem_compSet P d).1 (compMinF_mem P d i)

lemma compMin_eq_of_reach {i j : Fin n} (h : thrReach P d i j) : compMin P d i = compMin P d j := by
  rw [compMin_eq_min', compMin_eq_min']
  congr 1
  simp only [compSet_eq P d h]

lemma reach_of_compMin_eq {i j : Fin n} (h : compMin P d i = compMin P d j) : thrReach P d i j := by
  have hi := reach_compMin P d i
  have hj := reach_compMin P d j
  have : compMinF P d i = compMinF P d j := Fin.ext h
  rw [this] at hi
  exact thrReach_trans P d hi (thrReach_symm P d hj)

lemma compMin_eq_iff (i j : Fin n) : compMin P d i = compMin P d j ↔ thrReach P d i j :=
  ⟨reach_of_compMin_eq P d, compMin_eq_of_reach P d⟩

lemma isRep_iff (i : Fin n) : IsRep P d i ↔ compMin P d i = i := by
  constructor
  · intro h
    refine le_antisymm (compMin_le P d i) ?_
    have := h (compMinF P d i) (thrReach_symm P d (reach_compMin P d i))
    exact_mod_cast this
  · intro h j hj
    have h1 := compMin_eq_of_reach P d (thrReach_symm P d hj)
    have h2 := compMin_le P d j
    rw [Fin.le_def]; omega

/-- `j` is in the component whose minimum is `i` iff its component minimum is `i`. -/
lemma reach_iff_compMin {i j : Fin n} (hi : compMin P d i = i) :
    thrReach P d i j ↔ compMin P d j = i := by
  rw [← compMin_eq_iff, hi]; exact ⟨fun h => h.symm, fun h => h.symm⟩

end Comp

/-! ### Sorted index lists -/

/-- A strictly increasing enumeration of `T` is `T.orderEmbOfFin`. -/
lemma eq_orderEmbOfFin {N k : ℕ} (T : Finset (Fin N)) (hk : T.card = k) (f : Fin k → Fin N)
    (hmem : ∀ x, f x ∈ T) (hmono : StrictMono f) : ∀ x, f x = T.orderEmbOfFin hk x := by
  intro x
  have := Finset.orderEmbOfFin_unique hk hmem hmono
  rw [this]

/-! ### The radius ladder -/

section Ladder

variable {N : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ)

lemma rhoOf_succ (S : Finset (Fin N)) (k : ℕ) :
    rhoOf Y δ S (k + 1) = rhoOf Y δ S k * (1 + δ / 4) := by
  unfold rhoOf; ring

lemma rhoOf_zero (S : Finset (Fin N)) (hδ : 0 < δ) :
    rhoOf Y δ S 0 = rmedOf Y S / 2 / 2 / (1 + δ / 4) := by
  unfold rhoOf; simp

/-- With `r_med > 0` the ladder reaches the top radius. -/
lemma ladder_exists (S : Finset (Fin N)) (hδ : 0 < δ) (hr : 0 < rmedOf Y S) :
    ∃ k, bOf Y δ S ≤ rhoOf Y δ S k := by
  have he : 1 < 1 + δ / 4 := by linarith
  obtain ⟨k, hk⟩ := pow_unbounded_of_one_lt (bOf Y δ S / (rmedOf Y S / 2 / 2 / (1 + δ / 4))) he
  refine ⟨k, ?_⟩
  have hpos : 0 < rmedOf Y S / 2 / 2 / (1 + δ / 4) := by positivity
  rw [div_lt_iff₀ hpos] at hk
  unfold rhoOf
  have : rmedOf Y S / 2 / 2 * (1 + δ / 4) ^ k / (1 + δ / 4) =
      (1 + δ / 4) ^ k * (rmedOf Y S / 2 / 2 / (1 + δ / 4)) := by ring
  rw [this]; exact hk.le

/-- `MOf` is the ladder block's `Nat.find + 1`. -/
lemma MOf_eq (S : Finset (Fin N)) (h : ∃ k, bOf Y δ S ≤ rhoOf Y δ S k) :
    MOf Y δ S = Nat.find h + 1 := by
  unfold MOf; rw [dif_pos h]

end Ladder

end DetANN.HPIM.PP

-- ===== PP_Spec =====
/-! Specifications for the driver of `P`: the global invariant, sorted index lists, the child
contracts as hypotheses on the blocks, and the statement of the node procedure. -/

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

variable {m N : ℕ}

/-- The frame size of the driver's call stack. -/
def FS : ℕ := 10

/-- The global invariant of the driver after initialisation. -/
structure GInv (Y : Fin N → EuclideanSpace ℝ (Fin m)) (δ : ℝ) (T0 : ℕ) (v0 : ℤ) (s : State) :
    Prop where
  pm : s.core.ptrs 1 = m
  pPA : s.core.ptrs 12 = 4
  pN : s.core.ptrs 23 = N
  r0 : s.core.regs 0 = δ
  r1 : s.core.regs 1 = 1 + δ / 4
  r2 : s.core.regs 2 = lamOf N δ
  r20 : s.core.regs 20 = 0
  r21 : s.core.regs 21 = 2
  r22 : s.core.regs 22 = 4
  i1 : s.integerMemory 1 = m
  i2 : s.integerMemory 2 = v0
  i3 : s.integerMemory 3 = 4 + N
  pa : ∀ g : Fin N, s.integerMemory (4 + g) = 1 + g * m
  pow : ∀ t ≤ T0, s.integerMemory (4 + N + t) = 2 ^ t
  pts : ∀ (g : Fin N) (j : Fin m), s.core.mem (1 + g * m + j) = Y g j

/-- The sorted global indices of `S` are stored from integer address `a`. -/
def SList {N : ℕ} (s : State) (a : ℤ) (S : Finset (Fin N)) : Prop :=
  ∀ i : Fin S.card, s.integerMemory (a + i) = ((S.orderEmbOfFin rfl i : Fin N) : ℕ)

/-- The heap starts above the tables: `4 + N + T0 + 1`. -/
def Hbase (N T0 : ℕ) : ℤ := 4 + N + T0 + 1

/-! ### The child contracts, as hypotheses on the blocks -/

/-- `median_block` for `B.med` (constant `C`). -/
def MedOK (B : Blocks) (C : ℕ) : Prop :=
  ∀ (off : ℕ) (Q : Program), Embeds Q (B.med off) off →
  ∀ (m n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin m)) (s : State),
    1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false →
    LocalPts s (fun i j => pts i j) → s.core.ptrs 13 ≤ 0 →
    ∃ t, (run Q s detTape t).core.pc = off + B.Lm ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.regs 10 = medThreshold pts ∧
      KeepsLow s (run Q s detTape t) [] [10] ∧
      WritesOnly Q s t (fun c => c.1 = false ∧
        s.core.ptrs 13 - C * (n + 1) ≤ c.2 ∧ c.2 < s.core.ptrs 13) ∧
      (run Q s detTape t).work ≤ s.work + C * (n + 1) ^ 5 * (m + 1)

/-- `comps_block` for `B.comps` (constant `C`). -/
def CompsOK (B : Blocks) (C : ℕ) : Prop :=
  ∀ (off : ℕ) (Q : Program), Embeds Q (B.comps off) off →
  ∀ (m n : ℕ) (pts : Fin n → EuclideanSpace ℝ (Fin m)) (d : ℝ) (s : State),
    1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false →
    LocalPts s (fun i j => pts i j) → s.core.regs 10 = d → 0 ≤ d → s.core.ptrs 13 ≤ 0 →
    ∃ t, (run Q s detTape t).core.pc = off + B.Lc ∧ (run Q s detTape t).halted = false ∧
      (∀ i : Fin n, (run Q s detTape t).integerMemory (s.core.ptrs 13 - 1 - i) = compMin pts d i) ∧
      KeepsLow s (run Q s detTape t) [] [] ∧
      WritesOnly Q s t (fun c => c.1 = false ∧
        s.core.ptrs 13 - C * (n + 1) ≤ c.2 ∧ c.2 < s.core.ptrs 13) ∧
      (run Q s detTape t).work ≤ s.work + C * (n + 1) ^ 3 * (m + 1)

/-- `build_block` for `B.build` (constant `C`). -/
def BuildOK (B : Blocks) (C : ℕ) : Prop :=
  ∀ (off : ℕ) (Q : Program), Embeds Q (B.build off) off →
  ∀ (m n f : ℕ) (pts : Fin n → Fin m → ℝ) (r c : ℝ) (lo hi : Fin m → ℝ) (s : State),
    1 ≤ m → 1 ≤ n → s.core.pc = off → s.halted = false → LocalPts s pts →
    s.core.regs 11 = r → s.core.regs 12 = c → 0 ≤ s.core.ptrs 17 →
    (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + j) = lo j) →
    (∀ j : Fin m, s.core.mem (s.core.ptrs 17 + m + j) = hi j) →
    s.core.ptrs 13 ≤ 0 → s.core.ptrs 14 ≤ 0 → ¬ Starves pts r c f lo hi →
    ∃ t, (run Q s detTape t).core.pc = off + B.Lb ∧ (run Q s detTape t).halted = false ∧
      BSPAt m (run Q s detTape t) ((run Q s detTape t).core.ptrs 13) (s.core.ptrs 13)
        ((run Q s detTape t).core.ptrs 14) (s.core.ptrs 14) ((run Q s detTape t).core.ptrs 17)
        (build pts r c f lo hi) ∧
      KeepsLow s (run Q s detTape t) [13, 14, 17] [] ∧
      s.core.ptrs 13 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
        (run Q s detTape t).core.ptrs 13 ∧
      s.core.ptrs 14 - C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤
        (run Q s detTape t).core.ptrs 14 ∧
      WritesOnly Q s t (fun w =>
        (if w.1 then s.core.ptrs 14 else s.core.ptrs 13) -
            C * ((build pts r c f lo hi).paths.card + 1) * (m + 1) ≤ w.2 ∧
          w.2 < (if w.1 then s.core.ptrs 14 else s.core.ptrs 13)) ∧
      (run Q s detTape t).work ≤ s.work +
        C * ((build pts r c f lo hi).paths.card + 1) ^ 2 * (n + 1) * (m + 1) ^ 2

/-- `balance_block` for `B.bal` (constant `C`). -/
def BalOK (B : Blocks) (C : ℕ) : Prop :=
  ∀ (off : ℕ) (Q : Program), Embeds Q (B.bal off) off →
  ∀ (m : ℕ) (T : BSP m) (s : State) (ilo ihi rlo rhi : ℤ),
    1 ≤ m → s.core.pc = off → s.halted = false → s.core.ptrs 1 = m →
    BSPAt m s ilo ihi rlo rhi (s.core.ptrs 17) T → ihi ≤ 0 → rhi ≤ 0 →
    s.core.ptrs 13 ≤ ilo → s.core.ptrs 14 ≤ rlo → 0 ≤ s.core.ptrs 15 → 0 ≤ s.core.ptrs 16 →
    ∃ t, (run Q s detTape t).core.pc = off + B.Lbal ∧ (run Q s detTape t).halted = false ∧
      (∀ s'' : State,
        (∀ z, s.core.ptrs 15 ≤ z → z < (run Q s detTape t).core.ptrs 15 →
          s''.integerMemory z = (run Q s detTape t).integerMemory z) →
        (∀ z, s.core.ptrs 16 ≤ z → z < (run Q s detTape t).core.ptrs 16 →
          s''.core.mem z = (run Q s detTape t).core.mem z) →
        BoxTreeAt m s'' ((run Q s detTape t).core.ptrs 17) (balance T (T.paths.card + 1) [] ∅)) ∧
      KeepsLow s (run Q s detTape t) [15, 16, 17] [] ∧
      s.core.ptrs 15 ≤ (run Q s detTape t).core.ptrs 15 ∧
      (run Q s detTape t).core.ptrs 15 ≤ s.core.ptrs 15 + C * (T.paths.card + 1) ∧
      s.core.ptrs 16 ≤ (run Q s detTape t).core.ptrs 16 ∧
      (run Q s detTape t).core.ptrs 16 ≤ s.core.ptrs 16 + C * (T.paths.card + 1) * m ∧
      WritesOnly Q s t (fun c =>
        ((if c.1 then s.core.ptrs 14 else s.core.ptrs 13) - C * (T.paths.card + 1) ≤ c.2 ∧
          c.2 < (if c.1 then s.core.ptrs 14 else s.core.ptrs 13)) ∨
        ((if c.1 then s.core.ptrs 16 else s.core.ptrs 15) ≤ c.2 ∧
          c.2 < (if c.1 then (run Q s detTape t).core.ptrs 16
            else (run Q s detTape t).core.ptrs 15))) ∧
      (run Q s detTape t).work ≤ s.work + C * (T.paths.card + 1) ^ 2 * (m + 1)

/-- All four child contracts. -/
structure ChildOK (B : Blocks) where
  Cm : ℕ
  Cc : ℕ
  Cb : ℕ
  Cbal : ℕ
  med : MedOK B Cm
  comps : CompsOK B Cc
  build : BuildOK B Cb
  bal : BalOK B Cbal

end DetANN.HPIM.PP

-- ===== PP_Ret =====
/-! The RETURN segment (`seg14`, from `off + 82`): pop the frame at `p8`. -/

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The ten cells of a call frame at `F`: code, `v`, `i`, `n`, `S`, `Znode`, `Kids`, `vr`, `FP`,
`ZRnode`. -/
def FrameAt (s : State) (F : ℤ) (fr : Fin 10 → ℤ) : Prop := ∀ k : Fin 10, s.integerMemory (F + k) = fr k

/-- The frame registers, in frame order after the code. -/
def frameRegs : Fin 10 → ℕ := ![0, 2, 3, 11, 10, 20, 19, 21, 8, 28]

/-- Code `0`: halt. -/
lemma ret_halt (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State)
    (hpc : s.core.pc = off + 82) (hh : s.halted = false) (hc : s.integerMemory (s.core.ptrs 8) = 0) :
    (run Q s detTape 4).halted = true ∧ (run Q s detTape 4).integerMemory = s.integerMemory ∧
      (run Q s detTape 4).core.mem = s.core.mem ∧ (run Q s detTape 4).work = s.work + 4 := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hc; subst hpc hh
  (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
  rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Function.update_apply]
  rw [if_pos (by simp [hc])]
  rw [run_exec_at (i := 106) hE rfl rfl rfl]; simp only [exec, run_zero]
  refine ⟨?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-- Code `≥ 1`: restore `v, i, n, S, Znode, Kids, vr, ZRnode, FP` and jump to `KN`. -/
lemma ret_resume (Q : Program) (off KN : ℕ) (hE : Embeds Q (seg14 off KN) off) (s : State)
    (hpc : s.core.pc = off + 82) (hh : s.halted = false) (fr : Fin 10 → ℤ)
    (hF : FrameAt s (s.core.ptrs 8) fr) (hc : 1 ≤ fr 0) :
    (run Q s detTape 24).core.pc = off + 76 ∧ (run Q s detTape 24).halted = false ∧
      (∀ k : Fin 10, k ≠ 0 → (run Q s detTape 24).core.ptrs (frameRegs k) = fr k) ∧
      (∀ x, x ∉ [2, 3, 11, 10, 20, 19, 21, 8, 28, 6, 27, 9] →
        (run Q s detTape 24).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 24).core.regs = s.core.regs ∧
      (run Q s detTape 24).integerMemory = s.integerMemory ∧
      (run Q s detTape 24).core.mem = s.core.mem ∧ (run Q s detTape 24).work = s.work + 24 := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hF; subst hpc hh
  have f0 : im (ptrs 8) = fr 0 := by simpa using hF 0
  have f1 : im (ptrs 8 + 1) = fr 1 := hF 1
  have f2 : im (ptrs 8 + 2) = fr 2 := hF 2
  have f3 : im (ptrs 8 + 3) = fr 3 := hF 3
  have f4 : im (ptrs 8 + 4) = fr 4 := hF 4
  have f5 : im (ptrs 8 + 5) = fr 5 := hF 5
  have f6 : im (ptrs 8 + 6) = fr 6 := hF 6
  have f7 : im (ptrs 8 + 7) = fr 7 := hF 7
  have f8 : im (ptrs 8 + 8) = fr 8 := hF 8
  have f9 : im (ptrs 8 + 9) = fr 9 := hF 9
  (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
  rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Function.update_apply]
  rw [if_neg (by simp [f0]; omega)]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
  (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd]); (rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec, Nat.add_assoc, Nat.reduceAdd])
  rw [run_exec_at hE rfl rfl rfl]; simp only [exec, coreExec]
  rw [if_pos le_rfl, run_zero]
  refine ⟨rfl, rfl, ?_, ?_, rfl, rfl, rfl, rfl⟩
  · intro k hk
    fin_cases k
    · exact absurd rfl hk
    all_goals
      simp (config := {decide := true}) only [frameRegs, Fin.reduceFinMk, Fin.isValue,
        Matrix.cons_val, Function.update_apply, if_true, if_false, add_assoc, Int.reduceAdd,
        add_sub_assoc, Int.reduceSub]
      first | exact f1 | exact f2 | exact f3 | exact f4 | exact f5 | exact f6 | exact f7 | exact f8 | exact f9
  · intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
    obtain ⟨h2, h3, h11, h10, h20, h19, h21, h8, h28, h6, h27, h9⟩ := hx
    simp only [Function.update_apply, h2, h3, h11, h10, h20, h19, h21, h8, h28, h6, h27, h9,
      if_false]

end DetANN.HPIM.PP

-- ===== PP_Step =====
/-! Stepping `run` and `cellsWritten` together through an embedded block. -/

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN DetANN.HPIM

/-- The cell stored to by instruction `ins` in state `s`. -/
def wcell (ins : Instr) (s : State) : Option (Bool × ℤ) :=
  match ins with
  | .core (.store q _) => some (true, s.core.ptrs q)
  | .integerStore a _ => some (false, s.core.ptrs a)
  | _ => none

lemma cw_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i) (hB : B[i]? = some ins) :
    cellsWritten Q s (n + 1) = (wcell ins s).toFinset ∪ cellsWritten Q (exec detTape ins s) n := by
  have hQ : Q[s.core.pc]? = some ins := by rw [hpc]; exact hE i ins hB
  rw [show n + 1 = 1 + n by omega, cellsWritten_add]
  congr 1
  · simp only [cellsWritten, Finset.range_one, Finset.singleton_biUnion, run_zero, writtenCell, hh,
      Bool.false_eq_true, if_false, hQ]
    cases ins with
    | core i => cases i <;> rfl
    | _ => rfl
  · rw [run_succ, run_zero, step_eq_exec Q detTape s ins hh hQ]

/-- A step through an embedded block, for `run` and `cellsWritten` together. -/

lemma cw_zero (Q : Program) (s : State) : cellsWritten Q s 0 = ∅ := cellsWritten_zero Q s

/-! ### The node head (`seg2`, from `off + 39`) -/

/-- A single point: `I[v] = 0`, `I[v+1] = I[S]`, then `RETURN`. -/
lemma node_single (Q : Program) (off RET : ℕ) (hE : Embeds Q (seg2 off RET) off) (s : State)
    (hpc : s.core.pc = off + 39) (hh : s.halted = false) (v Sa : ℤ) (hv : s.core.ptrs 2 = v)
    (h3 : s.integerMemory (v + 3) = Sa) (h7 : s.integerMemory (v + 7) = 1) (hv1 : Sa ≠ v) :
    (run Q s detTape 15).core.pc = RET ∧ (run Q s detTape 15).halted = false ∧
      (run Q s detTape 15).integerMemory =
        Function.update (Function.update s.integerMemory v 0) (v + 1) (s.integerMemory Sa) ∧
      (run Q s detTape 15).core.mem = s.core.mem ∧ (run Q s detTape 15).core.regs = s.core.regs ∧
      (∀ x, x ∉ [6, 7, 10, 11, 27] → (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 15).work = s.work + 15 ∧
      cellsWritten Q s 15 ⊆ {(false, v), (false, v + 1)} := by
  obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
  simp only at hpc hh hv h3 h7; subst hpc hh hv
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell, Function.update_apply]
  rw [if_neg (by simp [h7])]
  simp only [Nat.add_assoc, Nat.reduceAdd]
  (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl])
  rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]
  simp only [exec, coreExec, wcell]
  rw [if_pos le_rfl, run_zero, cw_zero]
  simp (config := {decide := true}) only [Function.update_apply, if_true, if_false]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> try (first | rfl | trivial)
  · rw [h3, if_neg hv1]
  all_goals first
    | (intro c hc
       simp only [Option.toFinset_none, Option.toFinset_some, Finset.empty_union,
         Finset.union_empty, Finset.mem_union, Finset.mem_singleton] at hc
       simp only [Finset.mem_insert, Finset.mem_singleton]
       rcases hc with h | h <;> subst h <;> simp)
    | (intro x hx
       simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
       simp (config := {decide := true}) [Function.update_apply, hx])

end DetANN.HPIM.PP

-- ===== BB_Prog =====
/-! The balancing block: preorder records of the stored BSP, subtree sizes, and the centroid
recursion with a mark array and an explicit frame stack.

Records (integer scratch below `A` = pointer `13`): record `k` holds at `A − 5 + f − 5k` the field
`f`: `0` kind (`I[node]`), `1` node address, `2` subtree size, `3` mark, `4` component count (the
link of the DFS stack while walking). Frames of 4 cells (`j`, centroid, output node, fuel) grow
down from `A − 5N`.

Pointers: `41` `N`, `42` cur, `43` DFS top, `44`, `45` temporaries, `46` loop index, `47` frame
pointer, `48` frame base, `49` fuel, `50` `j`, `51` size, `52` total, `53` best, `54` best score,
`55` output node, `56`–`58` temporaries, `60`–`64` field bases `A − 5 + f`, `67`, `72`, `73`
5×index, `68` record index, `69` zero, `70` `−1`, `71` link, `74` end. Real `40` temporary. -/

namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM

lemma len0 (off : ℕ) : (bb0 off).length = 64 := rfl
lemma len1 (off : ℕ) : (bb1 off).length = 64 := rfl
lemma len2 (off : ℕ) : (bb2 off).length = 64 := rfl
lemma len3 (off : ℕ) : (bb3 off).length = 62 := rfl

lemma bb_len (off : ℕ) : (bb off).length = 254 := by
  simp only [bb, List.length_append, len0, len1, len2, len3]

lemma det0 (off : ℕ) : DetProgram (bb0 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bb0 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)

lemma det1 (off : ℕ) : DetProgram (bb1 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bb1 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)

lemma det2 (off : ℕ) : DetProgram (bb2 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bb2 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)

lemma det3 (off : ℕ) : DetProgram (bb3 off) := by
  apply DetANN.HPIM.PP.det_of_good
  intro op hop
  unfold bb3 at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨0, ?_⟩; norm_num; done)

lemma bb_det (off : ℕ) : DetProgram (bb off) := by
  unfold bb
  exact DetANN.HPIM.PP.det_append (det0 off) (DetANN.HPIM.PP.det_append (det1 off)
    (DetANN.HPIM.PP.det_append (det2 off) (det3 off)))

lemma bb_block : IsBlock bb 254 := fun off => ⟨bb_len off, bb_det off⟩

end DetANN.HPIM.BB

-- ===== BB_Lay =====
/-! Layout helpers for the balancing block: stored BSP nodes, the stability of the output box tree,
and the constant registers. -/

namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/- A step through the block, deciding address and branch conditions by `omega`. -/


/-- The kind cell of a stored node. -/
def kindOf : BSP m → ℤ
  | .leaf .. => 0
  | .cut .. => 1

/-- The answer encoding (`0` null, `i + 1`). -/
def enc : Option ℕ → ℤ
  | none => 0
  | some i => (i : ℤ) + 1

lemma kindOf_cut_or (T : BSP m) : (kindOf T = 0 ∧ ∃ lo hi a, T = .leaf lo hi a) ∨
    (kindOf T = 1 ∧ ∃ lo hi l r, T = .cut lo hi l r) := by
  cases T with
  | leaf lo hi a => exact Or.inl ⟨rfl, lo, hi, a, rfl⟩
  | cut lo hi l r => exact Or.inr ⟨rfl, lo, hi, l, r, rfl⟩

lemma bspat_congr {s s' : State} {ilo ihi rlo rhi u : ℤ} {T : BSP m}
    (h : BSPAt m s ilo ihi rlo rhi u T)
    (hI : ∀ z, ilo ≤ z → z < ihi → s'.integerMemory z = s.integerMemory z)
    (hR : ∀ z, rlo ≤ z → z < rhi → s'.core.mem z = s.core.mem z) :
    BSPAt m s' ilo ihi rlo rhi u T := by
  induction h with
  | leaf u lo hi a h1 h2 h3 h4 h5 h6 h7 h8 =>
    have e0 := hI u (by omega) (by omega)
    have e1 := hI (u + 1) (by omega) (by omega)
    have e2 := hI (u + 2) (by omega) (by omega)
    refine BSPAt.leaf u lo hi a h1 h2 (by rw [e0]; exact h3) (by rw [e1]; exact h4)
      (by rw [e1]; exact h5) ?_ ?_ (by rw [e2]; exact h8)
    · intro j; have := j.isLt; rw [e1, hR _ (by omega) (by omega)]; exact h6 j
    · intro j; have := j.isLt; rw [e1, hR _ (by omega) (by omega)]; exact h7 j
  | cut u lo hi l r h1 h2 h3 h4 h5 h6 h7 _ _ ihl ihr =>
    have e0 := hI u (by omega) (by omega)
    have e1 := hI (u + 1) (by omega) (by omega)
    have e2 := hI (u + 2) (by omega) (by omega)
    have e3 := hI (u + 3) (by omega) (by omega)
    refine BSPAt.cut u lo hi l r h1 h2 (by rw [e0]; exact h3) (by rw [e1]; exact h4)
      (by rw [e1]; exact h5) ?_ ?_ (by rw [e2]; exact ihl) (by rw [e3]; exact ihr)
    · intro j; have := j.isLt; rw [e1, hR _ (by omega) (by omega)]; exact h6 j
    · intro j; have := j.isLt; rw [e1, hR _ (by omega) (by omega)]; exact h7 j

/-- What a stored node provides. -/
lemma bsp_info {s : State} {ilo ihi rlo rhi u : ℤ} {T : BSP m}
    (h : BSPAt m s ilo ihi rlo rhi u T) :
    ilo ≤ u ∧ u + 3 ≤ ihi ∧ s.integerMemory u = kindOf T ∧ rlo ≤ s.integerMemory (u + 1) ∧
      s.integerMemory (u + 1) + 2 * m ≤ rhi ∧
      (∀ j : Fin m, s.core.mem (s.integerMemory (u + 1) + j) = T.box.1 j) ∧
      (∀ j : Fin m, s.core.mem (s.integerMemory (u + 1) + m + j) = T.box.2 j) := by
  cases h with
  | leaf u lo hi a h1 h2 h3 h4 h5 h6 h7 h8 => exact ⟨h1, h2, h3, h4, h5, h6, h7⟩
  | cut u lo hi l r h1 h2 h3 h4 h5 h6 h7 _ _ => exact ⟨h1, by omega, h3, h4, h5, h6, h7⟩

lemma bsp_ans {s : State} {ilo ihi rlo rhi u : ℤ} {lo hi : Fin m → ℝ} {a : Option ℕ}
    (h : BSPAt m s ilo ihi rlo rhi u (.leaf lo hi a)) : s.integerMemory (u + 2) = enc a := by
  cases h with
  | leaf u lo hi a h1 h2 h3 h4 h5 h6 h7 h8 => rw [h8]; cases a <;> rfl

lemma bsp_cut {s : State} {ilo ihi rlo rhi u : ℤ} {lo hi : Fin m → ℝ} {l r : BSP m}
    (h : BSPAt m s ilo ihi rlo rhi u (.cut lo hi l r)) :
    u + 4 ≤ ihi ∧ BSPAt m s ilo ihi rlo rhi (s.integerMemory (u + 2)) l ∧
      BSPAt m s ilo ihi rlo rhi (s.integerMemory (u + 3)) r := by
  cases h with
  | cut u lo hi l r h1 h2 h3 h4 h5 h6 h7 hl hr => exact ⟨h2, hl, hr⟩

/-- The output tree `B` is stored at `u` with all its cells in `[u, u')` (integer) and `[v, v')`
(real), stably under any change outside these ranges. -/
def Good (s : State) (u v u' v' : ℤ) (B : BoxTree m) : Prop :=
  ∀ s'' : State, (∀ z, u ≤ z → z < u' → s''.integerMemory z = s.integerMemory z) →
    (∀ z, v ≤ z → z < v' → s''.core.mem z = s.core.mem z) → BoxTreeAt m s'' u B

lemma good_mono {s s2 : State} {u v u' v' : ℤ} {B : BoxTree m} (h : Good s u v u' v' B)
    (hI : ∀ z, u ≤ z → z < u' → s2.integerMemory z = s.integerMemory z)
    (hM : ∀ z, v ≤ z → z < v' → s2.core.mem z = s.core.mem z) : Good s2 u v u' v' B :=
  fun s'' h1 h2 => h s'' (fun z a b => (h1 z a b).trans (hI z a b)) (fun z a b => (h2 z a b).trans (hM z a b))

lemma good_leaf {s : State} {u v v' : ℤ} (a : Option ℕ) (h0 : s.integerMemory u = 0)
    (h1 : s.integerMemory (u + 1) = enc a) : Good (m := m) s u v (u + 2) v' (.leaf a) := by
  intro s'' hI _
  refine BoxTreeAt.leaf u a (by rw [hI u le_rfl (by omega)]; exact h0) ?_
  rw [hI (u + 1) (by omega) (by omega), h1]
  cases a <;> rfl

lemma good_test {s : State} (lo hi : Fin m → ℝ) (y n : BoxTree m) (u v u1 v1 u2 v2 : ℤ) (hv : 0 ≤ v)
    (h0 : s.integerMemory u = 1) (h1 : s.integerMemory (u + 1) = v)
    (h2 : s.integerMemory (u + 2) = u + 4) (h3 : s.integerMemory (u + 3) = u1)
    (hlo : ∀ j : Fin m, s.core.mem (v + j) = lo j) (hhi : ∀ j : Fin m, s.core.mem (v + m + j) = hi j)
    (hy : Good s (u + 4) (v + 2 * m) u1 v1 y) (hn : Good s u1 v1 u2 v2 n)
    (o1 : u + 4 ≤ u1) (o2 : u1 ≤ u2) (o3 : v + 2 * m ≤ v1) (o4 : v1 ≤ v2) :
    Good s u v u2 v2 (.test lo hi y n) := by
  intro s'' hI hM
  have e0 := hI u le_rfl (by omega)
  have e1 := hI (u + 1) (by omega) (by omega)
  have e2 := hI (u + 2) (by omega) (by omega)
  have e3 := hI (u + 3) (by omega) (by omega)
  refine BoxTreeAt.test u lo hi y n (by rw [e0, h0]) (by rw [e1, h1]; exact hv) ?_ ?_ ?_ ?_
  · intro j; have := j.isLt; rw [e1, h1, hM _ (by omega) (by omega)]; exact hlo j
  · intro j; have := j.isLt; rw [e1, h1, hM _ (by omega) (by omega)]; exact hhi j
  · rw [e2, h2]
    exact hy s'' (fun z a b => hI z (by omega) (by omega)) (fun z a b => hM z (by omega) (by omega))
  · rw [e3, h3]
    exact hn s'' (fun z a b => hI z (by omega) (by omega)) (fun z a b => hM z (by omega) (by omega))

lemma consts_of {s s' : State} {A : ℤ} (h : Consts s A)
    (hf : ∀ x, x = 13 ∨ (60 ≤ x ∧ x ≤ 64) ∨ x = 69 ∨ x = 70 → s'.core.ptrs x = s.core.ptrs x) :
    Consts s' A := by
  obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := h
  exact ⟨by rw [hf 13 (by omega), c13], by rw [hf 60 (by omega), c60], by rw [hf 61 (by omega), c61],
    by rw [hf 62 (by omega), c62], by rw [hf 63 (by omega), c63], by rw [hf 64 (by omega), c64],
    by rw [hf 69 (by omega), c69], by rw [hf 70 (by omega), c70]⟩

end DetANN.HPIM.BB

-- ===== SegStep =====
/-! Stepping through a short sub-block embedded at `off + c`, with program counters `off + n`. -/

namespace DetANN.HPIM.SegStep

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP

lemma embeds_app_right {Q A B : Program} {o : ℕ} (h : Embeds Q (A ++ B) o) :
    Embeds Q B (o + A.length) := by
  intro i x hx
  have := h (A.length + i) x (by rw [List.getElem?_append_right (by omega)]; simpa using hx)
  rwa [← Nat.add_assoc] at this

lemma embeds_app_left {Q A B : Program} {o : ℕ} (h : Embeds Q (A ++ B) o) : Embeds Q A o := by
  intro i x hx
  exact h i x (by rw [List.getElem?_append_left (List.getElem?_eq_some_iff.1 hx).1]; exact hx)

lemma run_exec_seg {Q B : Program} {off c n i : ℕ} {ins : Instr} (hE : Embeds Q B (off + c))
    {s : State} {ω : ℕ → Bool} {k : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + n)
    (hn : i + c = n) (hB : B[i]? = some ins) : run Q s ω (k + 1) = run Q (exec ω ins s) ω k :=
  run_exec_at hE hh (by rw [hpc]; omega) hB

lemma cw_exec_seg {Q B : Program} {off c n i : ℕ} {ins : Instr} (hE : Embeds Q B (off + c))
    {s : State} {k : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + n) (hn : i + c = n)
    (hB : B[i]? = some ins) :
    cellsWritten Q s (k + 1) = (wcell ins s).toFinset ∪ cellsWritten Q (exec detTape ins s) k :=
  cw_exec_at hE hh (by rw [hpc]; omega) hB

end DetANN.HPIM.SegStep

-- ===== T32_Step =====
/-! The stepping tactic for the milestone 21 programs (as `zstp` of the BSP block). -/

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP


end DetANN.Supplement.Thm32

-- ===== T32_EvProg =====
/-! Lengths, determinism and the part embeddings of `ev`. -/

namespace DetANN.Supplement.Thm32

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.SegStep DetANN.HPIM.PP

lemma len_evA (off : ℕ) : (evA off).length = 43 := rfl
lemma len_fw (off : ℕ) : (fw off).length = 23 := rfl
lemma len_evB (off : ℕ) : (evB off).length = 14 := rfl

lemma ev_len (off : ℕ) : (ev off).length = 80 := by
  simp only [ev, List.length_append, len_evA, len_fw, len_evB]

lemma emb_evA {Q : Program} {off : ℕ} (hE : Embeds Q (ev off) off) : Embeds Q (evA off) (off + 0) := by
  have h := embeds_app_left (embeds_app_left hE)
  simpa only [Nat.add_zero] using h

lemma emb_fw {Q : Program} {off : ℕ} (hE : Embeds Q (ev off) off) :
    Embeds Q (fw (off + 43)) (off + 43) := by
  have h := embeds_app_right (embeds_app_left hE)
  simpa only [len_evA] using h

lemma emb_evB {Q : Program} {off : ℕ} (hE : Embeds Q (ev off) off) : Embeds Q (evB off) (off + 66) := by
  have h := embeds_app_right hE
  simpa only [List.length_append, len_evA, len_fw, Nat.add_assoc, Nat.reduceAdd] using h

lemma det_fw (off : ℕ) : DetProgram (fw off) := by
  apply det_of_good
  intro op hop
  unfold fw at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals trivial

lemma det_evA (off : ℕ) : DetProgram (evA off) := by
  apply det_of_good
  intro op hop
  unfold evA at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals first
    | trivial
    | (refine ⟨1, ?_⟩; norm_num; done)

lemma det_evB (off : ℕ) : DetProgram (evB off) := by
  apply det_of_good
  intro op hop
  unfold evB at hop
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hop
  repeat' rcases hop with rfl | hop
  all_goals refine ⟨?_, ⟨(fun r h => by cases h), (fun r a e h => by cases h)⟩⟩
  all_goals trivial

lemma ev_det (off : ℕ) : DetProgram (ev off) :=
  det_append (det_append (det_evA off) (det_fw (off + 43))) (det_evB off)

end DetANN.Supplement.Thm32

-- ===== T11_Emb =====
namespace DetANN.Thm11

open PNormReg PNormRegLib DetANN.Supplement.Thm32 DetANN.HPIM.SegStep

lemma emb_of_eq {Q B : Program} (h : Q = B) : Embeds Q B 0 := fun i x hx => by subst h; simpa using hx

lemma emb_trans {Q M B : Program} {o : ℕ} (h1 : Embeds Q M 0) (h2 : Embeds M B o) : Embeds Q B o :=
  fun i x hx => by simpa using h1 (o + i) x (h2 i x hx)

lemma len_reloc (p : RelocParams) (P : Program) : (reloc p P).length = 2 * P.length := by
  unfold reloc
  induction P with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons, List.length_append, List.length_cons, List.length_nil, ih]; ring

lemma len_pre (q : ℚ) : (pre q 0).length = 407 := by
  have a : (preA q 0).length = 41 := rfl
  have b0 : (preB0 q 0).length = 51 := rfl
  have b1 : (preB1 q 0).length = 73 := rfl
  have b2 : (preB2 q 0).length = 53 := rfl
  have b3 : (preB3 q 0).length = 41 := rfl
  have b4 : (preB4 q 0).length = 48 := rfl
  have b5 : (preB5 q 0).length = 67 := rfl
  have b6 : (preB6 q 0).length = 10 := rfl
  simp only [pre, List.length_append, a, b0, b1, b2, b3, b4, b5, b6, len_fw]

lemma len_reloc_pre {p : RelocParams} {q : ℚ} : (reloc p (pre q 0)).length = 814 := by
  rw [len_reloc, len_pre]

lemma len_reloc_ev {p : RelocParams} : (reloc p (ev 0)).length = 160 := by
  rw [len_reloc, ev_len]

lemma len_zeroRegs (r q a b : ℕ) : (zeroRegs r q a b).length = a + b := by
  simp [zeroRegs]

/-! Lengths and positions of the pieces of the outer programs. -/
lemma len_opre0 (c0 Cb K Cp X3 : ℕ) : (opre0 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre1 (c0 Cb K Cp X3 : ℕ) : (opre1 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre2 (c0 Cb K Cp X3 : ℕ) : (opre2 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre3 (c0 Cb K Cp X3 : ℕ) : (opre3 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre4 (c0 Cb K Cp X3 : ℕ) : (opre4 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre5 (c0 Cb K Cp X3 : ℕ) : (opre5 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre6 (c0 Cb K Cp X3 : ℕ) : (opre6 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre7 (c0 Cb K Cp X3 : ℕ) : (opre7 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre8 (c0 Cb K Cp X3 : ℕ) : (opre8 c0 Cb K Cp X3).length = 5 := rfl

lemma len_opre9 (c0 Cb K Cp X3 : ℕ) : (opre9 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre10 (c0 Cb K Cp X3 : ℕ) : (opre10 c0 Cb K Cp X3).length = 31 := rfl

lemma len_opre11 (c0 Cb K Cp X3 : ℕ) : (opre11 c0 Cb K Cp X3).length = 60 := rfl

lemma len_opre12 (c0 Cb K Cp X3 : ℕ) : (opre12 c0 Cb K Cp X3).length = 2 := rfl

lemma emb_opre0 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3) 0 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h))))))))))))))
  simpa only [List.length_append, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre1 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre1 c0 Cb K Cp X3) 60 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h))))))))))))))
  simpa only [List.length_append, len_opre0, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre2 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre2 c0 Cb K Cp X3) 120 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h)))))))))))))
  simpa only [List.length_append, len_opre0, len_opre1, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre3 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre3 c0 Cb K Cp X3) 180 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h))))))))))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre4 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre4 c0 Cb K Cp X3) 240 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h)))))))))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, len_opre3, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre5 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre5 c0 Cb K Cp X3) 300 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h))))))))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, len_opre3, len_opre4, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre6 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre6 c0 Cb K Cp X3) 360 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h)))))))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, len_opre3, len_opre4, len_opre5, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre7 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre7 c0 Cb K Cp X3) 420 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h))))))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre8 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre8 c0 Cb K Cp X3) 480 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h)))))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, len_opre7, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_pre (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0)) 485 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h))))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, len_opre7, len_opre8, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre9 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre9 c0 Cb K Cp X3) 1299 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (embeds_app_left (h)))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, len_opre7, len_opre8, len_reloc_pre, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre10 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre10 c0 Cb K Cp X3) 1359 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (embeds_app_left (h))))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, len_opre7, len_opre8, len_opre9, len_reloc_pre, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_ev_pre (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0)) 1390 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (embeds_app_left (h)))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre10, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, len_opre7, len_opre8, len_opre9, len_reloc_pre, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre11 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre11 c0 Cb K Cp X3) 1550 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (h))
  simpa only [List.length_append, len_opre0, len_opre1, len_opre10, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, len_opre7, len_opre8, len_opre9, len_reloc_ev, len_reloc_pre, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_opre12 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPreMain c0 Cb K Cp X3) (opre12 c0 Cb K Cp X3) 1610 := by
  have h : Embeds (outerPreMain c0 Cb K Cp X3) (opre0 c0 Cb K Cp X3 ++ opre1 c0 Cb K Cp X3 ++ opre2 c0 Cb K Cp X3 ++ opre3 c0 Cb K Cp X3 ++ opre4 c0 Cb K Cp X3 ++ opre5 c0 Cb K Cp X3 ++ opre6 c0 Cb K Cp X3 ++ opre7 c0 Cb K Cp X3 ++ opre8 c0 Cb K Cp X3 ++ reloc ⟨485, 100, 100, 46, 50, 1299⟩ (pre (c0 : ℚ) 0) ++ opre9 c0 Cb K Cp X3 ++ opre10 c0 Cb K Cp X3 ++ reloc ⟨1390, 200, 200, 46, 50, 1550⟩ (ev 0) ++ opre11 c0 Cb K Cp X3 ++ opre12 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (h)
  simpa only [List.length_append, len_opre0, len_opre1, len_opre10, len_opre11, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, len_opre7, len_opre8, len_opre9, len_reloc_ev, len_reloc_pre, Nat.zero_add, Nat.reduceAdd] using h2

lemma len_outerPreMain (c0 Cb K Cp X3 : ℕ) : (outerPreMain c0 Cb K Cp X3).length = 1612 := by
  simp only [outerPreMain, List.length_append, len_opre0, len_opre1, len_opre10, len_opre11, len_opre12, len_opre2, len_opre3, len_opre4, len_opre5, len_opre6, len_opre7, len_opre8, len_opre9, len_reloc_ev, len_reloc_pre]

lemma len_oqry0 (c0 Cb K Cp X3 : ℕ) : (oqry0 c0 Cb K Cp X3).length = 37 := rfl

lemma len_oqry1 (c0 Cb K Cp X3 : ℕ) : (oqry1 c0 Cb K Cp X3).length = 58 := rfl

lemma emb_oqry0 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerQryMain c0 Cb K Cp X3) (oqry0 c0 Cb K Cp X3) 0 := by
  have h : Embeds (outerQryMain c0 Cb K Cp X3) (oqry0 c0 Cb K Cp X3 ++ reloc ⟨37, 200, 200, 46, 50, 197⟩ (ev 0) ++ oqry1 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_left (embeds_app_left (h))
  simpa only [List.length_append, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_ev_q (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerQryMain c0 Cb K Cp X3) (reloc ⟨37, 200, 200, 46, 50, 197⟩ (ev 0)) 37 := by
  have h : Embeds (outerQryMain c0 Cb K Cp X3) (oqry0 c0 Cb K Cp X3 ++ reloc ⟨37, 200, 200, 46, 50, 197⟩ (ev 0) ++ oqry1 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (embeds_app_left (h))
  simpa only [List.length_append, len_oqry0, Nat.zero_add, Nat.reduceAdd] using h2

lemma emb_oqry1 (c0 Cb K Cp X3 : ℕ) :
    Embeds (outerQryMain c0 Cb K Cp X3) (oqry1 c0 Cb K Cp X3) 197 := by
  have h : Embeds (outerQryMain c0 Cb K Cp X3) (oqry0 c0 Cb K Cp X3 ++ reloc ⟨37, 200, 200, 46, 50, 197⟩ (ev 0) ++ oqry1 c0 Cb K Cp X3) 0 := emb_of_eq rfl
  have h2 := embeds_app_right (h)
  simpa only [List.length_append, len_oqry0, len_reloc_ev, Nat.zero_add, Nat.reduceAdd] using h2

lemma len_outerQryMain (c0 Cb K Cp X3 : ℕ) : (outerQryMain c0 Cb K Cp X3).length = 255 := by
  simp only [outerQryMain, List.length_append, len_oqry0, len_oqry1, len_reloc_ev]

/-! The main parts and the end subroutines inside the full programs. -/

lemma emb_preMain (Pre₃ : Program) (n3 c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPre Pre₃ n3 c0 Cb K Cp X3) (outerPreMain c0 Cb K Cp X3) 0 :=
  embeds_app_left (emb_of_eq rfl)

lemma emb_preZero (Pre₃ : Program) (n3 c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPre Pre₃ n3 c0 Cb K Cp X3) (zeroRegs 300 300 n3 n3) 1612 := by
  have h := embeds_app_left (embeds_app_right (emb_of_eq (rfl : outerPre Pre₃ n3 c0 Cb K Cp X3 = _)))
  simpa only [len_outerPreMain, Nat.zero_add] using h

lemma emb_preInner (Pre₃ : Program) (n3 c0 Cb K Cp X3 : ℕ) :
    Embeds (outerPre Pre₃ n3 c0 Cb K Cp X3)
      (reloc ⟨1612 + 2 * n3, 300, 300, 59, 62, 1582⟩ Pre₃) (1612 + 2 * n3) := by
  have h := embeds_app_right (embeds_app_right (emb_of_eq (rfl : outerPre Pre₃ n3 c0 Cb K Cp X3 = _)))
  simpa only [len_outerPreMain, len_zeroRegs, Nat.zero_add, two_mul] using h

lemma emb_qryMain (Qry₃ : Program) (n3 c0 Cb K Cp X3 : ℕ) :
    Embeds (outerQry Qry₃ n3 c0 Cb K Cp X3) (outerQryMain c0 Cb K Cp X3) 0 :=
  embeds_app_left (emb_of_eq rfl)

lemma emb_qryZero (Qry₃ : Program) (n3 c0 Cb K Cp X3 : ℕ) :
    Embeds (outerQry Qry₃ n3 c0 Cb K Cp X3) (zeroRegs 300 300 n3 n3) 255 := by
  have h := embeds_app_left (embeds_app_right (emb_of_eq (rfl : outerQry Qry₃ n3 c0 Cb K Cp X3 = _)))
  simpa only [len_outerQryMain, Nat.zero_add] using h

lemma emb_qryInner (Qry₃ : Program) (n3 c0 Cb K Cp X3 : ℕ) :
    Embeds (outerQry Qry₃ n3 c0 Cb K Cp X3)
      (reloc ⟨255 + 2 * n3, 300, 300, 59, 62, 223⟩ Qry₃) (255 + 2 * n3) := by
  have h := embeds_app_right (embeds_app_right (emb_of_eq (rfl : outerQry Qry₃ n3 c0 Cb K Cp X3 = _)))
  simpa only [len_outerQryMain, len_zeroRegs, Nat.zero_add, two_mul] using h

end DetANN.Thm11

-- ===== T11_Small =====
/-! Theorem 1.1, the case of one point: the outer preprocessing halts at once (instruction 6 jumps
to the `halt` at 1611), and the outer query answers `0` (instruction 2 jumps to 253). -/

namespace DetANN.Thm11.Small

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP

lemma pjle_pc (ω : ℕ → Bool) (q q' t : ℕ) (s : State) :
    (exec ω (.core (.pjle q q' t)) s).core.pc = if s.core.ptrs q ≤ s.core.ptrs q' then t else s.core.pc + 1 := by
  simp only [exec, coreExec]; split <;> rfl

lemma inp_im0 {d : ℕ} (P : Fin 1 → EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    (inputState P ε).integerMemory 0 = 1 := by
  simp [inputState, initState]

lemma pre_small (Pre₃ : Program) (n3 c0 Cb K Cp X3 d : ℕ) (P : Fin 1 → EuclideanSpace ℝ (Fin d)) (ε : ℝ) :
    (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape 8).halted = true ∧
    (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape 8).work = 8 ∧
    cellsWritten (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) 8 = ∅ ∧
    (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape 8).integerMemory =
      (inputState P ε).integerMemory := by
  have E0 := emb_trans (emb_preMain Pre₃ n3 c0 Cb K Cp X3) (emb_opre0 c0 Cb K Cp X3)
  have E12 := emb_trans (emb_preMain Pre₃ n3 c0 Cb K Cp X3) (emb_opre12 c0 Cb K Cp X3)
  have e0 : (opre0 c0 Cb K Cp X3)[0]? = some (.core (.pset 1 1)) := rfl
  have e1 : (opre0 c0 Cb K Cp X3)[1]? = some (.core (.pset 2 2)) := rfl
  have e2 : (opre0 c0 Cb K Cp X3)[2]? = some (.integerLoad 3 0) := rfl
  have e3 : (opre0 c0 Cb K Cp X3)[3]? = some (.integerLoad 4 1) := rfl
  have e4 : (opre0 c0 Cb K Cp X3)[4]? = some (.core (.load 0 0)) := rfl
  have e5 : (opre0 c0 Cb K Cp X3)[5]? = some (.core (.const 1 (0 : ℝ))) := rfl
  have e6 : (opre0 c0 Cb K Cp X3)[6]? = some (.core (.pjle 3 1 1611)) := rfl
  have e7 : (opre12 c0 Cb K Cp X3)[1]? = some .halt := rfl
  have im0 := inp_im0 P ε
  set s := inputState P ε with hs
  have pc0 : s.core.pc = 0 := rfl
  have h0 : s.halted = false := rfl
  have w0 : s.work = 0 := rfl
  have p0 : ∀ q, s.core.ptrs q = 0 := fun _ => rfl
  set s1 := exec detTape (.core (.pset 1 1)) s with hs1
  set s2 := exec detTape (.core (.pset 2 2)) s1 with hs2
  set s3 := exec detTape (.integerLoad 3 0) s2 with hs3
  set s4 := exec detTape (.integerLoad 4 1) s3 with hs4
  set s5 := exec detTape (.core (.load 0 0)) s4 with hs5
  set s6 := exec detTape (.core (.const 1 (0 : ℝ))) s5 with hs6
  set s7 := exec detTape (.core (.pjle 3 1 1611)) s6 with hs7
  set s8 := exec detTape .halt s7 with hs8
  have hh : ∀ x ∈ [s1, s2, s3, s4, s5, s6, s7], x.halted = false := by
    simp [hs7, hs6, hs5, hs4, hs3, hs2, hs1, exec, h0]
  have pc6 : s6.core.pc = 6 := by simp [hs6, hs5, hs4, hs3, hs2, hs1, exec, coreExec, pc0]
  have g6 : s6.core.ptrs 3 = 1 ∧ s6.core.ptrs 1 = 1 := by
    simp [hs6, hs5, hs4, hs3, hs2, hs1, exec, coreExec, Function.update_apply, p0, im0]
  have pc7 : s7.core.pc = 1611 := by rw [hs7, pjle_pc, if_pos (by rw [g6.1, g6.2])]
  have hpc : ∀ i : ℕ, i < 6 → ([s, s1, s2, s3, s4, s5][i]?.map (fun x => x.core.pc)) = some i := by
    intro i hi
    interval_cases i <;> simp [hs5, hs4, hs3, hs2, hs1, exec, coreExec, pc0]
  have q1 := hpc 1 (by norm_num); have q2 := hpc 2 (by norm_num); have q3 := hpc 3 (by norm_num)
  have q4 := hpc 4 (by norm_num); have q5 := hpc 5 (by norm_num)
  simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.map_some] at q1 q2 q3 q4 q5
  have H := fun x (hx : x ∈ [s1, s2, s3, s4, s5, s6, s7]) => hh x hx
  have hr : run (outerPre Pre₃ n3 c0 Cb K Cp X3) s detTape 8 = s8 := by
    rw [run_exec_at E0 h0 (by rw [pc0]) e0, run_exec_at E0 (H s1 (by simp)) (by rw [Option.some_inj.1 q1]) e1,
      run_exec_at E0 (H s2 (by simp)) (by rw [Option.some_inj.1 q2]) e2,
      run_exec_at E0 (H s3 (by simp)) (by rw [Option.some_inj.1 q3]) e3,
      run_exec_at E0 (H s4 (by simp)) (by rw [Option.some_inj.1 q4]) e4,
      run_exec_at E0 (H s5 (by simp)) (by rw [Option.some_inj.1 q5]) e5,
      run_exec_at E0 (H s6 (by simp)) (by rw [pc6]) e6,
      run_exec_at E12 (H s7 (by simp)) (by rw [pc7]) e7]
    rfl
  have hc : cellsWritten (outerPre Pre₃ n3 c0 Cb K Cp X3) s 8 = ∅ := by
    rw [cw_exec_at E0 h0 (by rw [pc0]) e0, cw_exec_at E0 (H s1 (by simp)) (by rw [Option.some_inj.1 q1]) e1,
      cw_exec_at E0 (H s2 (by simp)) (by rw [Option.some_inj.1 q2]) e2,
      cw_exec_at E0 (H s3 (by simp)) (by rw [Option.some_inj.1 q3]) e3,
      cw_exec_at E0 (H s4 (by simp)) (by rw [Option.some_inj.1 q4]) e4,
      cw_exec_at E0 (H s5 (by simp)) (by rw [Option.some_inj.1 q5]) e5,
      cw_exec_at E0 (H s6 (by simp)) (by rw [pc6]) e6,
      cw_exec_at E12 (H s7 (by simp)) (by rw [pc7]) e7]
    simp [wcell, cellsWritten]
  rw [hr, hc]
  refine ⟨by simp [hs8, exec], ?_, rfl, ?_⟩
  · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, exec, coreExec, w0]
  · simp [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1, exec, coreExec]

lemma qry_small (Qry₃ : Program) (n3 c0 Cb K Cp X3 d : ℕ) (s : State) (hs : s.integerMemory 0 = 1)
    (q : EuclideanSpace ℝ (Fin d)) :
    (run (outerQry Qry₃ n3 c0 Cb K Cp X3) (queryState d s q) detTape 5).halted = true ∧
    (run (outerQry Qry₃ n3 c0 Cb K Cp X3) (queryState d s q) detTape 5).work = 5 ∧
    (run (outerQry Qry₃ n3 c0 Cb K Cp X3) (queryState d s q) detTape 5).core.ptrs 0 = 0 := by
  have E0 := emb_trans (emb_qryMain Qry₃ n3 c0 Cb K Cp X3) (emb_oqry0 c0 Cb K Cp X3)
  have E1 := emb_trans (emb_qryMain Qry₃ n3 c0 Cb K Cp X3) (emb_oqry1 c0 Cb K Cp X3)
  have e0 : (oqry0 c0 Cb K Cp X3)[0]? = some (.core (.pset 1 1)) := rfl
  have e1 : (oqry0 c0 Cb K Cp X3)[1]? = some (.integerLoad 3 0) := rfl
  have e2 : (oqry0 c0 Cb K Cp X3)[2]? = some (.core (.pjle 3 1 253)) := rfl
  have e3 : (oqry1 c0 Cb K Cp X3)[56]? = some (.core (.pset 0 0)) := rfl
  have e4 : (oqry1 c0 Cb K Cp X3)[57]? = some .halt := rfl
  set u := queryState d s q with hu
  have pc0 : u.core.pc = 0 := rfl
  have h0 : u.halted = false := rfl
  have w0 : u.work = 0 := rfl
  have im0 : u.integerMemory 0 = 1 := hs
  have p0 : ∀ x, u.core.ptrs x = 0 := fun _ => rfl
  set u1 := exec detTape (.core (.pset 1 1)) u with hu1
  set u2 := exec detTape (.integerLoad 3 0) u1 with hu2
  set u3 := exec detTape (.core (.pjle 3 1 253)) u2 with hu3
  set u4 := exec detTape (.core (.pset 0 0)) u3 with hu4
  set u5 := exec detTape .halt u4 with hu5
  have g2 : u2.core.ptrs 3 = 1 ∧ u2.core.ptrs 1 = 1 := by
    simp [hu2, hu1, exec, coreExec, Function.update_apply, p0, im0]
  have pc1 : u1.core.pc = 1 := by simp [hu1, exec, coreExec, pc0]
  have pc2 : u2.core.pc = 2 := by simp [hu2, hu1, exec, coreExec, pc0]
  have pc3 : u3.core.pc = 253 := by rw [hu3, pjle_pc, if_pos (by rw [g2.1, g2.2])]
  have pc4 : u4.core.pc = 254 := by simp only [hu4, exec, coreExec, pc3]
  have hh : ∀ x ∈ [u1, u2, u3, u4], x.halted = false := by simp [hu4, hu3, hu2, hu1, exec, h0]
  have hr : run (outerQry Qry₃ n3 c0 Cb K Cp X3) u detTape 5 = u5 := by
    rw [run_exec_at E0 h0 (by rw [pc0]) e0, run_exec_at E0 (hh u1 (by simp)) (by rw [pc1]) e1,
      run_exec_at E0 (hh u2 (by simp)) (by rw [pc2]) e2,
      run_exec_at E1 (hh u3 (by simp)) (by rw [pc3]) e3,
      run_exec_at E1 (hh u4 (by simp)) (by rw [pc4]) e4]
    rfl
  rw [hr]
  exact ⟨by simp [hu5, exec], by simp [hu5, hu4, hu3, hu2, hu1, exec, coreExec, w0],
    by simp [hu5, hu4, exec, coreExec]⟩

end DetANN.Thm11.Small

namespace DetANN.Thm11

open PNormReg PNormRegLib DetANN

theorem outer_small_pf :
    ∀ (Pre₃ Qry₃ : Program) (n3 c0 Cb K Cp X3 d : ℕ) (P : Fin 1 → EuclideanSpace ℝ (Fin d)) (ε : ℝ),
      ∃ t : ℕ, t ≤ 8 ∧
        (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t).halted = true ∧
        (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t).work = t ∧
        cellsWritten (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) t = ∅ ∧
        ∀ q : EuclideanSpace ℝ (Fin d), ∃ t' : ℕ, t' ≤ 5 ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').halted = true ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').work = t' ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').core.ptrs 0 = 0 := by
  intro Pre₃ Qry₃ n3 c0 Cb K Cp X3 d P ε
  obtain ⟨a1, a2, a3, a4⟩ := Small.pre_small Pre₃ n3 c0 Cb K Cp X3 d P ε
  refine ⟨8, le_rfl, a1, a2, a3, fun q => ?_⟩
  have him : (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape 8).integerMemory 0 = 1 := by
    rw [a4]; exact Small.inp_im0 P ε
  obtain ⟨b1, b2, b3⟩ := Small.qry_small Qry₃ n3 c0 Cb K Cp X3 d _ him q
  exact ⟨5, le_rfl, b1, b2, b3⟩

end DetANN.Thm11

open PNormReg PNormRegLib DetANN DetANN.Thm11 in
theorem solution :
    ∀ (Pre₃ Qry₃ : Program) (n3 c0 Cb K Cp X3 d : ℕ) (P : Fin 1 → EuclideanSpace ℝ (Fin d)) (ε : ℝ),
      ∃ t : ℕ, t ≤ 8 ∧
        (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t).halted = true ∧
        (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t).work = t ∧
        cellsWritten (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) t = ∅ ∧
        ∀ q : EuclideanSpace ℝ (Fin d), ∃ t' : ℕ, t' ≤ 5 ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').halted = true ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').work = t' ∧
          (run (outerQry Qry₃ n3 c0 Cb K Cp X3)
            (queryState d (run (outerPre Pre₃ n3 c0 Cb K Cp X3) (inputState P ε) detTape t) q)
            detTape t').core.ptrs 0 = 0 :=
  DetANN.Thm11.outer_small_pf
