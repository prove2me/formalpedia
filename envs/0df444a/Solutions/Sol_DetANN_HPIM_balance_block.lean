-- Prove2me | solution 1 for DetANN.HPIM.balance_block
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-17T14:21:33.109842+00:00
-- url     : https://prove2.me/submissions/12cdac3e-2cbc-4d7c-8022-a245e71d0542

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
import Theorems.Thm_DetANN_HPIM_BB_walk_steps
import Theorems.Thm_DetANN_HPIM_BB_node_steps

-- ===== BB_Pre =====
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

end DetANN.HPIM.QP

-- ===== PP_Ladder =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP

/-- One step of a host `Q` through instruction `i` of an embedded block. -/
lemma run_exec_at {Q B : Program} {off i : ℕ} {ins : Instr} (hE : Embeds Q B off) {s : State}
    {ω : ℕ → Bool} {n : ℕ} (hh : s.halted = false) (hpc : s.core.pc = off + i)
    (hB : B[i]? = some ins) : run Q s ω (n + 1) = run Q (exec ω ins s) ω n :=
  run_exec hh (by rw [hpc]; exact hE i ins hB)

end DetANN.HPIM.PP

namespace DetANN.HPIM.PP

open PNormReg PNormRegLib DetANN.HPIM.QP

end DetANN.HPIM.PP

-- ===== PP_Prog =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth

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

/-- Offset of piece 1. -/
def o1 (B : Blocks) : ℕ := 39

/-- Offset of piece 2. -/
def o2 (B : Blocks) : ℕ := 39 + 14

/-- Offset of piece 3. -/
def o3 (B : Blocks) : ℕ := 39 + 14 + 58

/-- Offset of piece 4. -/
def o4 (B : Blocks) : ℕ := 39 + 14 + 58 + B.Lm

end Blocks

end DetANN.HPIM.PP

-- ===== PP_Basic =====
namespace DetANN.HPIM.PP

open PNormReg PNormRegLib SmaleNinth DetANN.HPIM.QP DetANN

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

variable (B : Blocks)

end DetANN.HPIM.PP

-- ===== PP_Det =====
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

end DetANN.HPIM.PP

-- ===== PP_Step =====
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

lemma cw_zero (Q : Program) (s : State) : cellsWritten Q s 0 = ∅ := cellsWritten_zero Q s

end DetANN.HPIM.PP

-- ===== BB_Prog =====
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
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

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

-- ===== BB_DFS =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- Offsets 0–14: constants, `N := 0`, `cur := root`, `top := −1`. -/
lemma seg_setup (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State)
    (hpc : s.core.pc = off) (hh : s.halted = false) :
    (run Q s detTape 15).core.pc = off + 15 ∧ (run Q s detTape 15).halted = false ∧
      Consts (run Q s detTape 15) (s.core.ptrs 13) ∧ (run Q s detTape 15).core.ptrs 41 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 15).core.ptrs 42 = s.core.ptrs 17 ∧ (run Q s detTape 15).core.ptrs 43 = -1 ∧
      (∀ x < 40, (run Q s detTape 15).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 15).core.regs = s.core.regs ∧ (run Q s detTape 15).core.mem = s.core.mem ∧
      (run Q s detTape 15).integerMemory = s.integerMemory ∧
      (run Q s detTape 15).work = s.work + 15 ∧ cellsWritten Q s 15 = ∅ :=
  walk_steps.1 Q off hE s hpc hh

/-- Offsets 15–25 at a leaf: record `n₀` := (kind `0`, address `u`), `N := n₀ + 1`, to `POP`. -/
lemma seg_leaf (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (n0 : ℕ) (s : State)
    (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u)
    (h41 : s.core.ptrs 41 = n0) (hu : A ≤ u) (hk : s.integerMemory u = 0) :
    (run Q s detTape 11).core.pc = off + 34 ∧ (run Q s detTape 11).halted = false ∧
      (run Q s detTape 11).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧
      (run Q s detTape 11).integerMemory (fa A 0 n0) = 0 ∧
      (run Q s detTape 11).integerMemory (fa A 1 n0) = u ∧
      (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → (run Q s detTape 11).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 41 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 →
        (run Q s detTape 11).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 11).core.regs = s.core.regs ∧ (run Q s detTape 11).core.mem = s.core.mem ∧
      (run Q s detTape 11).work = s.work + 11 ∧
      ∀ c ∈ cellsWritten Q s 11, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0) :=
  walk_steps.2.1 Q off hE A u n0 s hpc hh hC h42 h41 hu hk

/-- Offsets 15–33 at a cut: record `n₀` := (kind `1`, address `u`, link `tp`), push, to the left child. -/
lemma seg_cut (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tp : ℤ) (n0 : ℕ) (s : State)
    (hpc : s.core.pc = off + 15) (hh : s.halted = false) (hC : Consts s A) (h42 : s.core.ptrs 42 = u)
    (h41 : s.core.ptrs 41 = n0) (h43 : s.core.ptrs 43 = tp) (hu : A ≤ u) (hk : s.integerMemory u = 1) :
    (run Q s detTape 19).core.pc = off + 15 ∧ (run Q s detTape 19).halted = false ∧
      (run Q s detTape 19).core.ptrs 41 = ((n0 + 1 : ℕ) : ℤ) ∧
      (run Q s detTape 19).core.ptrs 42 = s.integerMemory (u + 2) ∧
      (run Q s detTape 19).core.ptrs 43 = n0 ∧
      (run Q s detTape 19).integerMemory (fa A 0 n0) = 1 ∧
      (run Q s detTape 19).integerMemory (fa A 1 n0) = u ∧
      (run Q s detTape 19).integerMemory (fa A 4 n0) = tp ∧
      (∀ z, z ≠ fa A 0 n0 → z ≠ fa A 1 n0 → z ≠ fa A 4 n0 →
        (run Q s detTape 19).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 41 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 →
        (run Q s detTape 19).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 19).core.regs = s.core.regs ∧ (run Q s detTape 19).core.mem = s.core.mem ∧
      (run Q s detTape 19).work = s.work + 19 ∧
      ∀ c ∈ cellsWritten Q s 19, c = (false, fa A 0 n0) ∨ c = (false, fa A 1 n0) ∨ c = (false, fa A 4 n0) :=
  walk_steps.2.2.1 Q off hE A u tp n0 s hpc hh hC h42 h41 h43 hu hk

/-- Offsets 34–47 with `top = k ≥ 0`: pop `k`, go to the right child of record `k`. -/
lemma seg_pop (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = k) :
    (run Q s detTape 14).core.pc = off + 15 ∧ (run Q s detTape 14).halted = false ∧
      (run Q s detTape 14).core.ptrs 42 = s.integerMemory (s.integerMemory (fa A 1 k) + 3) ∧
      (run Q s detTape 14).core.ptrs 43 = s.integerMemory (fa A 4 k) ∧
      (∀ x, x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 67 → x ≠ 71 →
        (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧
      (run Q s detTape 14).integerMemory = s.integerMemory ∧
      (run Q s detTape 14).work = s.work + 14 ∧ cellsWritten Q s 14 = ∅ :=
  walk_steps.2.2.2.1 Q off hE A k s hpc hh hC h43

/-- Offset 34 with `top = −1`: the walk is done. -/
lemma seg_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s : State)
    (hpc : s.core.pc = off + 34) (hh : s.halted = false) (hC : Consts s A) (h43 : s.core.ptrs 43 = -1) :
    (run Q s detTape 1).core.pc = off + 48 ∧ (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core = { s.core with pc := off + 48 } ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅ :=
  walk_steps.2.2.2.2.1 Q off hE A s hpc hh hC h43

lemma U_left (lo hi : Fin m → ℝ) (l r : BSP m) (i : ℕ) (h : i < size l) :
    U (.cut lo hi l r) (1 + i) = U l i := by unfold U; rw [nd_left lo hi l r i h]

lemma U_right (lo hi : Fin m → ℝ) (l r : BSP m) (i : ℕ) (h : i < size r) :
    U (.cut lo hi l r) (1 + size l + i) = U r i := by unfold U; rw [nd_right lo hi l r i h]

set_option maxHeartbeats 1000000 in
/-- **The walk of a stored subtree** (from `VISIT` to `POP`). -/
lemma visit (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (hA : A ≤ ilo) :
    ∀ (T : BSP m) (s : State) (u tp : ℤ) (n0 : ℕ),
      s.core.pc = off + 15 → s.halted = false → Consts s A →
      BSPAt m s0 ilo ihi rlo rhi u T →
      (∀ z, ilo ≤ z → z < ihi → s.integerMemory z = s0.integerMemory z) →
      s.core.ptrs 42 = u → s.core.ptrs 41 = n0 → s.core.ptrs 43 = tp →
      ∃ t, t ≤ 33 * size T ∧ (run Q s detTape t).core.pc = off + 34 ∧
        (run Q s detTape t).halted = false ∧ Consts (run Q s detTape t) A ∧
        (run Q s detTape t).core.ptrs 41 = ((n0 + size T : ℕ) : ℤ) ∧
        (run Q s detTape t).core.ptrs 43 = tp ∧
        (∀ i < size T, (run Q s detTape t).integerMemory (fa A 0 (n0 + i)) = kindOf (U T i) ∧
          BSPAt m s0 ilo ihi rlo rhi ((run Q s detTape t).integerMemory (fa A 1 (n0 + i))) (U T i)) ∧
        (∀ z, (z < A - 5 * ((n0 + size T : ℕ) : ℤ) ∨ A - 5 * (n0 : ℤ) ≤ z) →
          (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ x, x ≠ 41 → x ≠ 42 → x ≠ 43 → x ≠ 44 → x ≠ 45 → x ≠ 67 → x ≠ 68 → x ≠ 71 →
          (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t,
          c.1 = false ∧ A - 5 * ((n0 + size T : ℕ) : ℤ) ≤ c.2 ∧ c.2 < A - 5 * (n0 : ℤ) := by
  intro T
  induction T with
  | leaf lo hi a =>
    intro s u tp n0 hpc hh hC hB hag h42 h41 h43
    obtain ⟨b1, b2, b3, -⟩ := bsp_info hB
    have hk : s.integerMemory u = 0 := by rw [hag u b1 (by omega), b3]; rfl
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ :=
      seg_leaf Q off hE A u n0 s hpc hh hC h42 h41 (by omega) hk
    refine ⟨11, by simp [size], g1, g2,
      consts_of hC (fun x hx => g7 x (by omega) (by omega) (by omega) (by omega) (by omega)),
      by rw [g3]; simp [size], by rw [g7 43 (by omega) (by omega) (by omega) (by omega) (by omega)]; exact h43,
      ?_, ?_, ?_, g8, g9, g10, ?_⟩
    · intro i hi; simp only [size] at hi
      obtain rfl : i = 0 := by omega
      rw [U_zero, Nat.add_zero, g4, g5]; exact ⟨rfl, hB⟩
    · intro z hz
      simp only [size] at hz; push_cast at hz
      apply g6 <;> unfold fa <;> omega
    · intro x x1 x2 x3 x4 x5 x6 x7 x8; exact g7 x x1 x4 x5 x6 x7
    · intro c hc
      rcases g11 c hc with rfl | rfl <;> unfold fa <;> simp [size] <;> omega
  | cut lo hi l r ihl ihr =>
    intro s u tp n0 hpc hh hC hB hag h42 h41 h43
    have hs : size (BSP.cut lo hi l r) = 1 + size l + size r := rfl
    obtain ⟨b1, b2, b3, -⟩ := bsp_info hB
    obtain ⟨b4, hBl, hBr⟩ := bsp_cut hB
    have hk : s.integerMemory u = 1 := by rw [hag u b1 (by omega), b3]; rfl
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14⟩ :=
      seg_cut Q off hE A u tp n0 s hpc hh hC h42 h41 h43 (by omega) hk
    set s1 := run Q s detTape 19 with hs1
    have hC1 : Consts s1 A := consts_of hC (fun x hx => g10 x (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega))
    have hag1 : ∀ z, ilo ≤ z → z < ihi → s1.integerMemory z = s0.integerMemory z := by
      intro z z1 z2
      rw [g9 z (by unfold fa; omega) (by unfold fa; omega) (by unfold fa; omega), hag z z1 z2]
    have hul : s1.core.ptrs 42 = s0.integerMemory (u + 2) := by rw [g4, hag (u + 2) (by omega) (by omega)]
    obtain ⟨t2, ht2, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ :=
      ihl s1 _ (n0 : ℤ) (n0 + 1) g1 g2 hC1 hBl hag1 hul g3 g5
    set s2 := run Q s1 detTape t2 with hs2
    obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ := seg_pop Q off hE A n0 s2 l1 l2 l3 l5
    set s3 := run Q s2 detTape 14 with hs3
    have hr0 : s2.integerMemory (fa A 0 n0) = 1 := by
      rw [l7 _ (Or.inr (by unfold fa; push_cast; omega)), g6]
    have hr1 : s2.integerMemory (fa A 1 n0) = u := by
      rw [l7 _ (Or.inr (by unfold fa; push_cast; omega)), g7]
    have hr4 : s2.integerMemory (fa A 4 n0) = tp := by
      rw [l7 _ (Or.inr (by unfold fa; push_cast; omega)), g8]
    have hag2 : ∀ z, ilo ≤ z → z < ihi → s2.integerMemory z = s0.integerMemory z := by
      intro z z1 z2; rw [l7 z (Or.inr (by push_cast; omega)), hag1 z z1 z2]
    have hur : s3.core.ptrs 42 = s0.integerMemory (u + 3) := by
      rw [p3, hr1, hag2 (u + 3) (by omega) (by omega)]
    have hC3 : Consts s3 A := consts_of l3 (fun x hx => p5 x (by omega) (by omega) (by omega) (by omega)
      (by omega))
    have hag3 : ∀ z, ilo ≤ z → z < ihi → s3.integerMemory z = s0.integerMemory z := by
      intro z z1 z2; rw [p8, hag2 z z1 z2]
    have h41' : s3.core.ptrs 41 = ((n0 + 1 + size l : ℕ) : ℤ) := by
      rw [p5 41 (by omega) (by omega) (by omega) (by omega) (by omega), l4]
    obtain ⟨t4, ht4, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ :=
      ihr s3 _ tp (n0 + 1 + size l) p1 p2 hC3 hBr hag3 hur h41' (by rw [p4, hr4])
    set s4 := run Q s3 detTape t4 with hs4
    refine ⟨19 + t2 + 14 + t4, by rw [hs]; omega, ?_⟩
    have RR : run Q s detTape (19 + t2 + 14 + t4) = s4 := by
      rw [hs4, hs3, hs2, hs1]; simp only [← run_add]
    have CW : cellsWritten Q s (19 + t2 + 14 + t4) =
        cellsWritten Q s 19 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 14 ∪ cellsWritten Q s3 t4 := by
      rw [hs3, hs2, hs1]; simp only [cellsWritten_add, ← run_add]
    rw [RR, CW, p10]
    refine ⟨r1, r2, r3, by rw [r4, hs]; congr 1; omega, r5, ?_, ?_, ?_, by rw [r9, p6, l9, g11],
      by rw [r10, p7, l10, g12], by rw [r11, p9, l11, g13]; ring, ?_⟩
    · intro i hi2
      rcases cut_cases (size l) (size r) i (by omega) with h | ⟨i', h1, rfl⟩ | ⟨i', h1, rfl⟩
      · subst h; rw [U_zero, Nat.add_zero]
        have e0 : s4.integerMemory (fa A 0 n0) = 1 := by
          rw [r7 _ (Or.inr (by unfold fa; push_cast; omega)), p8, hr0]
        have e1 : s4.integerMemory (fa A 1 n0) = u := by
          rw [r7 _ (Or.inr (by unfold fa; push_cast; omega)), p8, hr1]
        rw [e0, e1]; exact ⟨rfl, hB⟩
      · rw [U_left lo hi l r i' h1, show n0 + (1 + i') = n0 + 1 + i' by omega]
        obtain ⟨q1, q2⟩ := l6 i' h1
        rw [r7 _ (Or.inr (by unfold fa; push_cast; omega)), p8, q1,
          r7 _ (Or.inr (by unfold fa; push_cast; omega)), p8]
        exact ⟨rfl, q2⟩
      · rw [U_right lo hi l r i' h1, show n0 + (1 + size l + i') = n0 + 1 + size l + i' by omega]
        exact r6 i' h1
    · intro z hz
      rw [hs] at hz; push_cast at hz
      rw [r7 z (by push_cast; omega), p8, l7 z (by push_cast; omega)]
      apply g9 <;> unfold fa <;> omega
    · intro x x1 x2 x3 x4 x5 x6 x7 x8
      rw [r8 x x1 x2 x3 x4 x5 x6 x7 x8, p5 x x2 x3 x4 x6 x8, l8 x x1 x2 x3 x4 x5 x6 x7 x8,
        g10 x x1 x2 x3 x4 x5 x6 x7]
    · intro c hc
      rw [hs]; push_cast
      simp only [Finset.union_empty, Finset.mem_union] at hc
      rcases hc with (hc | hc) | hc
      · rcases g14 c hc with rfl | rfl | rfl <;> unfold fa <;> simp <;> omega
      · obtain ⟨c1, c2, c3⟩ := l12 c hc; push_cast at c2 c3; exact ⟨c1, by omega, by omega⟩
      · obtain ⟨c1, c2, c3⟩ := r12 c hc; push_cast at c2 c3; exact ⟨c1, by omega, by omega⟩

end DetANN.HPIM.BB

-- ===== BB_Size =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- One backward step at a leaf record `k = i − 1`. -/
lemma sz_leaf (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (k : ℕ) (s : State)
    (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 0) :
    (run Q s detTape 14).core.pc = off + 49 ∧ (run Q s detTape 14).halted = false ∧
      (run Q s detTape 14).core.ptrs 46 = (k : ℤ) ∧
      (run Q s detTape 14).integerMemory (fa A 2 k) = 1 ∧
      (run Q s detTape 14).integerMemory (fa A 3 k) = 0 ∧
      (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 14).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 →
        (run Q s detTape 14).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 14).core.regs = s.core.regs ∧ (run Q s detTape 14).core.mem = s.core.mem ∧
      (run Q s detTape 14).work = s.work + 14 ∧
      ∀ c ∈ cellsWritten Q s 14, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k) :=
  walk_steps.2.2.2.2.2.1 Q off hE A k s hpc hh hC h46 hk

/-- One backward step at a cut record `k = i − 1`, with the sizes `a`, `b` of its children. -/
lemma sz_cut (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A a b : ℤ) (k : ℕ) (s : State)
    (hpc : s.core.pc = off + 49) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (hk : s.integerMemory (fa A 0 k) = 1)
    (ha : s.integerMemory (fa A 2 (k + 1)) = a)
    (hb : s.integerMemory (A - 3 - 5 * ((k : ℤ) + 1 + a)) = b) :
    (run Q s detTape 29).core.pc = off + 49 ∧ (run Q s detTape 29).halted = false ∧
      (run Q s detTape 29).core.ptrs 46 = (k : ℤ) ∧
      (run Q s detTape 29).integerMemory (fa A 2 k) = 1 + a + b ∧
      (run Q s detTape 29).integerMemory (fa A 3 k) = 0 ∧
      (∀ z, z ≠ fa A 2 k → z ≠ fa A 3 k → (run Q s detTape 29).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 →
        (run Q s detTape 29).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 29).core.regs = s.core.regs ∧ (run Q s detTape 29).core.mem = s.core.mem ∧
      (run Q s detTape 29).work = s.work + 29 ∧
      ∀ c ∈ cellsWritten Q s 29, c = (false, fa A 2 k) ∨ c = (false, fa A 3 k) :=
  walk_steps.2.2.2.2.2.2.1 Q off hE A a b k s hpc hh hC h46 hk ha hb

set_option maxHeartbeats 1000000 in
/-- **The backward pass** from `i` down to `0`. -/
lemma sz_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (T : BSP m) :
    ∀ (i : ℕ) (s : State), s.core.pc = off + 49 → s.halted = false → Consts s A →
      s.core.ptrs 46 = (i : ℤ) → i ≤ size T →
      (∀ k < size T, s.integerMemory (fa A 0 k) = kindOf (U T k)) →
      (∀ k, i ≤ k → k < size T → s.integerMemory (fa A 2 k) = S T k ∧ s.integerMemory (fa A 3 k) = 0) →
      ∃ t, t ≤ 29 * i + 1 ∧ (run Q s detTape t).core.pc = off + 78 ∧
        (run Q s detTape t).halted = false ∧
        (∀ k < size T, (run Q s detTape t).integerMemory (fa A 2 k) = S T k ∧
          (run Q s detTape t).integerMemory (fa A 3 k) = 0) ∧
        (∀ z, (∀ k : ℕ, k < i → z ≠ fa A 2 k ∧ z ≠ fa A 3 k) →
          (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 →
          (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ c ∈ cellsWritten Q s t, c.1 = false ∧ A - 5 * (i : ℤ) ≤ c.2 ∧ c.2 < A := by
  intro i
  induction i with
  | zero =>
    intro s hpc hh hC h46 _ _ hinv
    refine ⟨1, by omega, ?_⟩
    obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 hinv ⊢
    subst hh
    rw [hpc]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, fun k hk => hinv k (Nat.zero_le _) hk, fun z _ => rfl, fun x _ _ _ _ _ _ _ _ => rfl,
      rfl, rfl, rfl, by simp⟩
  | succ k ih =>
    intro s hpc hh hC h46 hiN hkind hinv
    have hkN : k < size T := by omega
    have hkk := hkind k hkN
    rcases kindOf_cut_or (U T k) with ⟨hk0, lo, hi, a, hU⟩ | ⟨hk1, lo, hi, l, r, hU⟩
    · rw [hk0] at hkk
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := sz_leaf Q off hE A k s hpc hh hC h46 hkk
      set s1 := run Q s detTape 14 with hs1
      have hC1 : Consts s1 A := consts_of hC (fun x hx => g7 x (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega))
      have hkind1 : ∀ k' < size T, s1.integerMemory (fa A 0 k') = kindOf (U T k') := by
        intro k' hk'; rw [g6 _ (by unfold fa; omega) (by unfold fa; omega)]; exact hkind k' hk'
      have hinv1 : ∀ k', k ≤ k' → k' < size T → s1.integerMemory (fa A 2 k') = S T k' ∧
          s1.integerMemory (fa A 3 k') = 0 := by
        intro k' k1 k2
        rcases Nat.eq_or_lt_of_le k1 with rfl | k1
        · refine ⟨?_, g5⟩; rw [g4]; unfold S; rw [hU]; rfl
        · obtain ⟨e1, e2⟩ := hinv k' k1 k2
          rw [g6 _ (by unfold fa; omega) (by unfold fa; omega), g6 _ (by unfold fa; omega)
            (by unfold fa; omega)]
          exact ⟨e1, e2⟩
      obtain ⟨t, ht, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
        ih s1 g1 g2 hC1 g3 (by omega) hkind1 hinv1
      refine ⟨14 + t, by omega, ?_⟩
      rw [run_add, cellsWritten_add, ← hs1]
      refine ⟨q1, q2, q3, ?_, ?_, by rw [q6, g8], by rw [q7, g9], by rw [q8, g10]; ring, ?_⟩
      · intro z hz
        rw [q4 z (fun k' hk' => hz k' (by omega)), g6 z (hz k (by omega)).1 (hz k (by omega)).2]
      · intro x x1 x2 x3 x4 x5 x6 x7 x8
        rw [q5 x x1 x2 x3 x4 x5 x6 x7 x8, g7 x x1 x2 x3 x4 x5 x6 x7 x8]
      · intro c hc
        rcases Finset.mem_union.1 hc with hc | hc
        · rcases g11 c hc with rfl | rfl <;> unfold fa <;> simp <;> omega
        · obtain ⟨c1, c2, c3⟩ := q9 c hc; exact ⟨c1, by push_cast; omega, c3⟩
    · rw [hk1] at hkk
      have hS := S_cut T k hkN lo hi l r hU
      have hb := bound T k hkN
      have hp1 : 1 ≤ S T (k + 1 + S T (k + 1)) := size_pos _
      have hp2 : 1 ≤ S T (k + 1) := size_pos _
      obtain ⟨a1, -⟩ := hinv (k + 1) le_rfl (by omega)
      obtain ⟨b1, -⟩ := hinv (k + 1 + S T (k + 1)) (by omega) (by omega)
      have hb1 : s.integerMemory (A - 3 - 5 * ((k : ℤ) + 1 + (S T (k + 1) : ℤ))) = S T (k + 1 + S T (k + 1)) := by
        rw [← b1]; unfold fa; congr 1; push_cast; ring
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ :=
        sz_cut Q off hE A _ _ k s hpc hh hC h46 hkk a1 hb1
      set s1 := run Q s detTape 29 with hs1
      have hC1 : Consts s1 A := consts_of hC (fun x hx => g7 x (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega))
      have hkind1 : ∀ k' < size T, s1.integerMemory (fa A 0 k') = kindOf (U T k') := by
        intro k' hk'; rw [g6 _ (by unfold fa; omega) (by unfold fa; omega)]; exact hkind k' hk'
      have hinv1 : ∀ k', k ≤ k' → k' < size T → s1.integerMemory (fa A 2 k') = S T k' ∧
          s1.integerMemory (fa A 3 k') = 0 := by
        intro k' k1 k2
        rcases Nat.eq_or_lt_of_le k1 with rfl | k1
        · refine ⟨?_, g5⟩; rw [g4, hS]; push_cast; ring
        · obtain ⟨e1, e2⟩ := hinv k' k1 k2
          rw [g6 _ (by unfold fa; omega) (by unfold fa; omega), g6 _ (by unfold fa; omega)
            (by unfold fa; omega)]
          exact ⟨e1, e2⟩
      obtain ⟨t, ht, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
        ih s1 g1 g2 hC1 g3 (by omega) hkind1 hinv1
      refine ⟨29 + t, by omega, ?_⟩
      rw [run_add, cellsWritten_add, ← hs1]
      refine ⟨q1, q2, q3, ?_, ?_, by rw [q6, g8], by rw [q7, g9], by rw [q8, g10]; ring, ?_⟩
      · intro z hz
        rw [q4 z (fun k' hk' => hz k' (by omega)), g6 z (hz k (by omega)).1 (hz k (by omega)).2]
      · intro x x1 x2 x3 x4 x5 x6 x7 x8
        rw [q5 x x1 x2 x3 x4 x5 x6 x7 x8, g7 x x1 x2 x3 x4 x5 x6 x7 x8]
      · intro c hc
        rcases Finset.mem_union.1 hc with hc | hc
        · rcases g11 c hc with rfl | rfl <;> unfold fa <;> simp <;> omega
        · obtain ⟨c1, c2, c3⟩ := q9 c hc; exact ⟨c1, by push_cast; omega, c3⟩

/-- Offsets 78–86: frame base `A − 5N`, fuel `N + 1`, `j := 0`, output root := pointer `15`. -/
lemma seg_start (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (N : ℕ) (s : State)
    (hpc : s.core.pc = off + 78) (hh : s.halted = false) (hC : Consts s A) (h41 : s.core.ptrs 41 = N) :
    (run Q s detTape 9).core.pc = off + 87 ∧ (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 48 = A - 5 * (N : ℤ) ∧
      (run Q s detTape 9).core.ptrs 47 = A - 5 * (N : ℤ) ∧
      (run Q s detTape 9).core.ptrs 49 = ((N + 1 : ℕ) : ℤ) ∧
      (run Q s detTape 9).core.ptrs 50 = ((0 : ℕ) : ℤ) ∧
      (run Q s detTape 9).core.ptrs 17 = s.core.ptrs 15 ∧
      (∀ x, x ≠ 17 → x ≠ 47 → x ≠ 48 → x ≠ 49 → x ≠ 50 → x ≠ 67 →
        (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅ :=
  walk_steps.2.2.2.2.2.2.2.1 Q off hE A N s hpc hh hC h41

end DetANN.HPIM.BB

-- ===== BB_Cnt =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- `CALL` with fuel `0`: write the leaf `none` at `u`, then `RET`. -/
lemma seg_fuel0 (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u : ℤ) (s : State)
    (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : s.core.ptrs 49 = 0)
    (h15 : s.core.ptrs 15 = u) :
    (run Q s detTape 10).core.pc = off + 218 ∧ (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 15 = u + 2 ∧
      (run Q s detTape 10).integerMemory u = 0 ∧ (run Q s detTape 10).integerMemory (u + 1) = 0 ∧
      (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape 10).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 56 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧
      (run Q s detTape 10).work = s.work + 10 ∧
      ∀ c ∈ cellsWritten Q s 10, c = (false, u) ∨ c = (false, u + 1) :=
  walk_steps.2.2.2.2.2.2.2.2.2.1 Q off hE A u s hpc hh hC h49 h15

/-- `CALL` with fuel `≥ 1`: `S := sz[j]`, `i := j + S`, to `CNT`. -/
lemma seg_head (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (j : ℕ) (s : State)
    (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : 1 ≤ s.core.ptrs 49)
    (h50 : s.core.ptrs 50 = j) :
    (run Q s detTape 7).core.pc = off + 94 ∧ (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 51 = s.integerMemory (fa A 2 j) ∧
      (run Q s detTape 7).core.ptrs 46 = j + s.integerMemory (fa A 2 j) ∧
      (run Q s detTape 7).core.ptrs 67 = 5 * (j : ℤ) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 51 → x ≠ 67 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 7).core.regs = s.core.regs ∧ (run Q s detTape 7).core.mem = s.core.mem ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧ cellsWritten Q s 7 = ∅ :=
  walk_steps.2.2.2.2.2.2.2.2.2.2.1 Q off hE A j s hpc hh hC h49 h50

/-- One count step at a leaf record `k` (`e` = 1 if unmarked, 0 if marked). -/
lemma cnt_leaf_seg (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e : ℤ) (k : ℕ)
    (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k)
    (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0))
    (hk : s.integerMemory (fa A 0 k) = 0) :
    ∃ t, t ≤ 16 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧
      (run Q s detTape t).integerMemory (fa A 4 k) = e ∧
      (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 →
        (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k) :=
  walk_steps.2.2.2.2.2.2.2.2.2.2.2.1 Q off hE A j e k s hpc hh hC h46 h50 hjk hm hk

/-- One count step at a cut record `k`: `cnt[k] := e + cnt[k+1] + cnt[k+1+sz[k+1]]`. -/
lemma cnt_cut_seg (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A j e a z b : ℤ) (k : ℕ)
    (s : State) (hpc : s.core.pc = off + 94) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ)) (h50 : s.core.ptrs 50 = j) (hjk : j ≤ k)
    (hm : (s.integerMemory (fa A 3 k) = 0 ∧ e = 1) ∨ (s.integerMemory (fa A 3 k) = 1 ∧ e = 0))
    (hk : s.integerMemory (fa A 0 k) = 1) (ha : s.integerMemory (fa A 4 (k + 1)) = a)
    (hz : s.integerMemory (fa A 2 (k + 1)) = z) (hb : s.integerMemory (A - 1 - 5 * ((k : ℤ) + 1 + z)) = b) :
    ∃ t, t ≤ 33 ∧ (run Q s detTape t).core.pc = off + 94 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 46 = (k : ℤ) ∧
      (run Q s detTape t).integerMemory (fa A 4 k) = e + a + b ∧
      (∀ z, z ≠ fa A 4 k → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 →
        (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, fa A 4 k) :=
  walk_steps.2.2.2.2.2.2.2.2.2.2.2.2 Q off hE A j e a z b k s hpc hh hC h46 h50 hjk hm hk ha hz hb

end DetANN.HPIM.BB

-- ===== BB_CntLoop =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- The records of `T` (kind, node address, subtree size) are in place. -/
def Recs (s0 : State) (ilo ihi rlo rhi A : ℤ) (T : BSP m) (s : State) : Prop :=
  ∀ k < size T, s.integerMemory (fa A 0 k) = kindOf (U T k) ∧
    BSPAt m s0 ilo ihi rlo rhi (s.integerMemory (fa A 1 k)) (U T k) ∧
    s.integerMemory (fa A 2 k) = S T k

/-- The marks represent the removed set `R`. -/
def Marks (A : ℤ) (T : BSP m) (R : Finset (List Bool)) (s : State) : Prop :=
  ∀ k < size T, s.integerMemory (fa A 3 k) = if unc T R k then 0 else 1

lemma recs_of {s0 s s' : State} {ilo ihi rlo rhi A : ℤ} {T : BSP m}
    (h : Recs s0 ilo ihi rlo rhi A T s)
    (hf : ∀ k < size T, ∀ f : ℤ, 0 ≤ f → f ≤ 2 → s'.integerMemory (fa A f k) = s.integerMemory (fa A f k)) :
    Recs s0 ilo ihi rlo rhi A T s' := by
  intro k hk
  obtain ⟨e0, e1, e2⟩ := h k hk
  rw [hf k hk 0 le_rfl (by norm_num), hf k hk 1 (by norm_num) (by norm_num),
    hf k hk 2 (by norm_num) le_rfl]
  exact ⟨e0, e1, e2⟩

lemma marks_of {s s' : State} {A : ℤ} {T : BSP m} {R : Finset (List Bool)} (h : Marks A T R s)
    (hf : ∀ k < size T, s'.integerMemory (fa A 3 k) = s.integerMemory (fa A 3 k)) : Marks A T R s' := by
  intro k hk; rw [hf k hk]; exact h k hk

lemma mark_e (A : ℤ) (T : BSP m) (R : Finset (List Bool)) (s : State) (k : ℕ)
    (hm : s.integerMemory (fa A 3 k) = if unc T R k then 0 else 1) :
    (s.integerMemory (fa A 3 k) = 0 ∧ ((if unc T R k then 1 else 0 : ℕ) : ℤ) = 1) ∨
      (s.integerMemory (fa A 3 k) = 1 ∧ ((if unc T R k then 1 else 0 : ℕ) : ℤ) = 0) := by
  by_cases hu : unc T R k
  · left; rw [hm, if_pos hu, if_pos hu]; simp
  · right; rw [hm, if_neg hu, if_neg hu]; simp

set_option maxHeartbeats 1000000 in
/-- **The count pass** over `[j, j + S j)` from the top down. -/
lemma cnt_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (T : BSP m) (R : Finset (List Bool)) (j : ℕ) (hj : j < size T) :
    ∀ (c : ℕ) (s : State), c ≤ S T j → s.core.pc = off + 94 → s.halted = false → Consts s A →
      s.core.ptrs 46 = ((j + c : ℕ) : ℤ) → s.core.ptrs 50 = j →
      Recs s0 ilo ihi rlo rhi A T s → Marks A T R s →
      (∀ k, j + c ≤ k → k < j + S T j → s.integerMemory (fa A 4 k) = cntI T R k) →
      ∃ t, t ≤ 33 * c + 1 ∧ (run Q s detTape t).core.pc = off + 127 ∧
        (run Q s detTape t).halted = false ∧
        (∀ k, j ≤ k → k < j + S T j → (run Q s detTape t).integerMemory (fa A 4 k) = cntI T R k) ∧
        (∀ z, (∀ k : ℕ, j ≤ k → k < j + c → z ≠ fa A 4 k) →
          (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 72 → x ≠ 73 →
          (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ w ∈ cellsWritten Q s t, ∃ k : ℕ, j ≤ k ∧ k < j + c ∧ w = (false, fa A 4 k) := by
  have hbj := bound T j hj
  intro c
  induction c with
  | zero =>
    intro s _ hpc hh hC h46 h50 _ _ hinv
    refine ⟨1, by omega, ?_⟩
    obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 h50 hinv ⊢
    subst hh
    rw [hpc]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, fun k k1 k2 => hinv k (by omega) k2, fun z _ => rfl,
      fun x _ _ _ _ _ _ _ _ => rfl, rfl, rfl, rfl, by simp⟩
  | succ c ih =>
    intro s hc hpc hh hC h46 h50 hR hM hinv
    set k := j + c with hkdef
    have hkN : k < size T := by omega
    have hkj : k < j + S T j := by omega
    obtain ⟨hk0, -, -⟩ := hR k hkN
    have hme := mark_e A T R s k (hM k hkN)
    have h46' : s.core.ptrs 46 = ((k + 1 : ℕ) : ℤ) := by rw [h46, hkdef]; push_cast; ring
    have hsub := sub_interval T j k hj (by omega) hkj
    rcases kindOf_cut_or (U T k) with ⟨hk, lo, hi, a, hU⟩ | ⟨hk, lo, hi, l, r, hU⟩
    · rw [hk] at hk0
      obtain ⟨t1, ht1, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
        cnt_leaf_seg Q off hE A j _ k s hpc hh hC h46' h50 (by omega) hme hk0
      set s1 := run Q s detTape t1 with hs1
      have hC1 : Consts s1 A := consts_of hC (fun x hx => g6 x (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega))
      have hR1 : Recs s0 ilo ihi rlo rhi A T s1 := recs_of hR (fun k' _ f f0 f1 => g5 _ (by unfold fa; omega))
      have hM1 : Marks A T R s1 := marks_of hM (fun k' _ => g5 _ (by unfold fa; omega))
      have hinv1 : ∀ k', j + c ≤ k' → k' < j + S T j → s1.integerMemory (fa A 4 k') = cntI T R k' := by
        intro k' k1 k2
        rcases Nat.eq_or_lt_of_le k1 with e | k1
        · rw [← e, g4, cnt_leaf T R k lo hi a hU]
        · rw [g5 _ (by unfold fa; omega)]; exact hinv k' k1 k2
      obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
        ih s1 (by omega) g1 g2 hC1 (by rw [g3]) (by rw [g6 50 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega), h50]) hR1 hM1 hinv1
      refine ⟨t1 + t2, by omega, ?_⟩
      rw [run_add, cellsWritten_add, ← hs1]
      refine ⟨q1, q2, q3, ?_, ?_, by rw [q6, g7], by rw [q7, g8], by rw [q8, g9]; ring, ?_⟩
      · intro z hz
        rw [q4 z (fun k' k1 k2 => hz k' k1 (by omega)), g5 z (hz k (by omega) (by omega))]
      · intro x x1 x2 x3 x4 x5 x6 x7 x8
        rw [q5 x x1 x2 x3 x4 x5 x6 x7 x8, g6 x x1 x2 x3 x4 x5 x6 x7 x8]
      · intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · exact ⟨k, by omega, by omega, g10 w hw⟩
        · obtain ⟨k', k1, k2, e⟩ := q9 w hw; exact ⟨k', k1, by omega, e⟩
    · rw [hk] at hk0
      have hS := S_cut T k hkN lo hi l r hU
      have hp1 : 1 ≤ S T (k + 1 + S T (k + 1)) := size_pos _
      have hp2 : 1 ≤ S T (k + 1) := size_pos _
      have ha := hinv (k + 1) (by omega) (by omega)
      have hz := (hR (k + 1) (by omega)).2.2
      have hb := hinv (k + 1 + S T (k + 1)) (by omega) (by omega)
      have hb' : s.integerMemory (A - 1 - 5 * ((k : ℤ) + 1 + (S T (k + 1) : ℤ))) =
          cntI T R (k + 1 + S T (k + 1)) := by
        rw [← hb]; unfold fa; congr 1; push_cast; ring
      obtain ⟨t1, ht1, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
        cnt_cut_seg Q off hE A j _ _ _ _ k s hpc hh hC h46' h50 (by omega) hme hk0 ha hz hb'
      set s1 := run Q s detTape t1 with hs1
      have hC1 : Consts s1 A := consts_of hC (fun x hx => g6 x (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega))
      have hR1 : Recs s0 ilo ihi rlo rhi A T s1 := recs_of hR (fun k' _ f f0 f1 => g5 _ (by unfold fa; omega))
      have hM1 : Marks A T R s1 := marks_of hM (fun k' _ => g5 _ (by unfold fa; omega))
      have hinv1 : ∀ k', j + c ≤ k' → k' < j + S T j → s1.integerMemory (fa A 4 k') = cntI T R k' := by
        intro k' k1 k2
        rcases Nat.eq_or_lt_of_le k1 with e | k1
        · rw [← e, g4, cnt_cut T R k hkN lo hi l r hU]; push_cast; ring
        · rw [g5 _ (by unfold fa; omega)]; exact hinv k' k1 k2
      obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
        ih s1 (by omega) g1 g2 hC1 (by rw [g3]) (by rw [g6 50 (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega) (by omega), h50]) hR1 hM1 hinv1
      refine ⟨t1 + t2, by omega, ?_⟩
      rw [run_add, cellsWritten_add, ← hs1]
      refine ⟨q1, q2, q3, ?_, ?_, by rw [q6, g7], by rw [q7, g8], by rw [q8, g9]; ring, ?_⟩
      · intro z hz
        rw [q4 z (fun k' k1 k2 => hz k' k1 (by omega)), g5 z (hz k (by omega) (by omega))]
      · intro x x1 x2 x3 x4 x5 x6 x7 x8
        rw [q5 x x1 x2 x3 x4 x5 x6 x7 x8, g6 x x1 x2 x3 x4 x5 x6 x7 x8]
      · intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · exact ⟨k, by omega, by omega, g10 w hw⟩
        · obtain ⟨k', k1, k2, e⟩ := q9 w hw; exact ⟨k', k1, by omega, e⟩

end DetANN.HPIM.BB

-- ===== BB_Scan =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- `total ≤ 1`: write the leaf with answer cell `av` at `u`, then `RET`. -/
lemma seg_leafout (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u tot av : ℤ) (j : ℕ)
    (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A)
    (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h15 : s.core.ptrs 15 = u) (htot : s.integerMemory (fa A 4 j) = tot)
    (htl : tot ≤ 1) (hu : A ≤ u)
    (hav : (s.integerMemory (fa A 0 j) = 0 ∧ s.integerMemory (s.integerMemory (fa A 1 j) + 2) = av) ∨
      (s.integerMemory (fa A 0 j) = 1 ∧ av = 0)) :
    ∃ t, t ≤ 20 ∧ (run Q s detTape t).core.pc = off + 218 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 15 = u + 2 ∧
      (run Q s detTape t).integerMemory u = 0 ∧ (run Q s detTape t).integerMemory (u + 1) = av ∧
      (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 45 → x ≠ 52 → x ≠ 56 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, u) ∨ c = (false, u + 1) :=
  node_steps.1 Q off hE A u tot av j s hpc hh hC h67 h15 htot htl hu hav

/-- `total ≥ 2`: `bs := total + 1`, `i := j`, `end := j + S`, to `SCAN`. -/
lemma seg_scan0 (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A tot : ℤ) (j : ℕ)
    (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A)
    (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h50 : s.core.ptrs 50 = j)
    (htot : s.integerMemory (fa A 4 j) = tot) (htl : 2 ≤ tot) :
    (run Q s detTape 8).core.pc = off + 135 ∧ (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 52 = tot ∧ (run Q s detTape 8).core.ptrs 54 = tot + 1 ∧
      (run Q s detTape 8).core.ptrs 46 = j ∧
      (run Q s detTape 8).core.ptrs 74 = j + s.core.ptrs 51 ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 52 → x ≠ 54 → x ≠ 56 → x ≠ 74 →
        (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).integerMemory = s.integerMemory ∧
      (run Q s detTape 8).work = s.work + 8 ∧ cellsWritten Q s 8 = ∅ :=
  node_steps.2.1 Q off hE A tot j s hpc hh hC h67 h50 htot htl

/-- `SCAN` with `end ≤ i + 1`: the scan is done. -/
lemma scan_exit (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A i e : ℤ) (s : State)
    (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = i) (h74 : s.core.ptrs 74 = e) (hie : e ≤ i + 1) :
    (run Q s detTape 2).core.pc = off + 153 ∧ (run Q s detTape 2).halted = false ∧
      (∀ x, x ≠ 46 → (run Q s detTape 2).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 2).core.regs = s.core.regs ∧ (run Q s detTape 2).core.mem = s.core.mem ∧
      (run Q s detTape 2).integerMemory = s.integerMemory ∧
      (run Q s detTape 2).work = s.work + 2 ∧ cellsWritten Q s 2 = ∅ :=
  node_steps.2.2.1 Q off hE A i e s hpc hh hC h46 h74 hie

/-- `SCAN` at a marked node `k = i + 1 < end`: skip. -/
lemma scan_marked (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e : ℤ) (k : ℕ) (s : State)
    (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e)
    (hm : s.integerMemory (fa A 3 k) = 1) :
    (run Q s detTape 9).core.pc = off + 135 ∧ (run Q s detTape 9).halted = false ∧
      (run Q s detTape 9).core.ptrs 46 = k ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 72 → (run Q s detTape 9).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 9).core.regs = s.core.regs ∧ (run Q s detTape 9).core.mem = s.core.mem ∧
      (run Q s detTape 9).integerMemory = s.integerMemory ∧
      (run Q s detTape 9).work = s.work + 9 ∧ cellsWritten Q s 9 = ∅ :=
  node_steps.2.2.2.1 Q off hE A e k s hpc hh hC h46 h74 hke hm

/-- `SCAN` at an unmarked node `k`: load its count into pointer `56` (offsets 135–145). -/
lemma scan_pre (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A e ci : ℤ) (k : ℕ)
    (s : State) (hpc : s.core.pc = off + 135) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 + 1 = k) (h74 : s.core.ptrs 74 = e) (hke : (k : ℤ) < e)
    (hm : s.integerMemory (fa A 3 k) = 0) (hci : s.integerMemory (fa A 4 k) = ci) :
    (run Q s detTape 10).core.pc = off + 146 ∧ (run Q s detTape 10).halted = false ∧
      (run Q s detTape 10).core.ptrs 46 = k ∧ (run Q s detTape 10).core.ptrs 56 = ci ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 56 → x ≠ 72 → (run Q s detTape 10).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 10).core.regs = s.core.regs ∧ (run Q s detTape 10).core.mem = s.core.mem ∧
      (run Q s detTape 10).integerMemory = s.integerMemory ∧
      (run Q s detTape 10).work = s.work + 10 ∧ cellsWritten Q s 10 = ∅ :=
  node_steps.2.2.2.2.1 Q off hE A e ci k s hpc hh hC h46 h74 hke hm hci

/-- Offsets 146–152: score `max ci (tot − ci)`; take `k` if it beats `bs`. -/
lemma scan_post (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (tot ci : ℤ) (s : State)
    (hpc : s.core.pc = off + 146) (hh : s.halted = false) (h52 : s.core.ptrs 52 = tot)
    (h56 : s.core.ptrs 56 = ci) :
    ∃ t, t ≤ 7 ∧ (run Q s detTape t).core.pc = off + 135 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 54 =
        (if max ci (tot - ci) < s.core.ptrs 54 then max ci (tot - ci) else s.core.ptrs 54) ∧
      (run Q s detTape t).core.ptrs 53 =
        (if max ci (tot - ci) < s.core.ptrs 54 then s.core.ptrs 46 else s.core.ptrs 53) ∧
      (∀ x, x ≠ 53 → x ≠ 54 → x ≠ 56 → x ≠ 57 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ :=
  node_steps.2.2.2.2.2.1 Q off hE tot ci s hpc hh h52 h56

end DetANN.HPIM.BB

-- ===== BB_ScanLoop =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- A centroid candidate of the component of `j`. -/
def cand (T : BSP m) (R : Finset (List Bool)) (j k : ℕ) : Prop := j < k ∧ k < j + S T j ∧ unc T R k

instance instDecCand (T : BSP m) (R : Finset (List Bool)) (j : ℕ) : DecidablePred (cand T R j) :=
  fun k => by unfold cand; infer_instance

lemma score_lt (T : BSP m) (R : Finset (List Bool)) (j : ℕ) (hj : j < size T) :
    ∀ k, cand T R j k → score T R j k < cntI T R j + 1 := by
  intro k ⟨k1, k2, _⟩
  have := cnt_le T R j k hj k1.le k2
  unfold score; omega

lemma score_cast (T : BSP m) (R : Finset (List Bool)) (j k : ℕ) (hj : j < size T) (k1 : j ≤ k)
    (k2 : k < j + S T j) :
    max (cntI T R k : ℤ) ((cntI T R j : ℤ) - cntI T R k) = (score T R j k : ℤ) := by
  have := cnt_le T R j k hj k1 k2
  unfold score
  rw [← Nat.cast_sub this]
  push_cast
  rfl

set_option maxHeartbeats 2000000 in
/-- **The scan** over the candidates `(j, j + S j)`. -/
lemma scan_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (T : BSP m)
    (R : Finset (List Bool)) (j : ℕ) (hj : j < size T) :
    ∀ (r d b bs : ℕ) (s : State), d + 1 + r = S T j →
      s.core.pc = off + 135 → s.halted = false → Consts s A →
      s.core.ptrs 46 = ((j + d : ℕ) : ℤ) → s.core.ptrs 74 = ((j + S T j : ℕ) : ℤ) →
      s.core.ptrs 52 = (cntI T R j : ℤ) → s.core.ptrs 54 = (bs : ℤ) →
      (bs < cntI T R j + 1 → s.core.ptrs 53 = b) →
      SInv (cand T R j) (score T R j) (cntI T R j + 1) (j + 1) (j + d + 1) b bs →
      Marks A T R s → (∀ k, j ≤ k → k < j + S T j → s.integerMemory (fa A 4 k) = cntI T R k) →
      ∃ t b' bs', t ≤ 17 * r + 2 ∧ (run Q s detTape t).core.pc = off + 153 ∧
        (run Q s detTape t).halted = false ∧
        SInv (cand T R j) (score T R j) (cntI T R j + 1) (j + 1) (j + S T j) b' bs' ∧
        (bs' < cntI T R j + 1 → (run Q s detTape t).core.ptrs 53 = b') ∧
        (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 53 → x ≠ 54 → x ≠ 56 → x ≠ 57 → x ≠ 72 →
          (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ := by
  have hbj := bound T j hj
  have hsc := score_lt T R j hj
  intro r
  induction r with
  | zero =>
    intro d b bs s hr hpc hh hC h46 h74 h52 h54 h53 hI hM hcnt
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      scan_exit Q off hE A _ _ s hpc hh hC h46 h74 (by push_cast; omega)
    refine ⟨2, b, bs, by omega, g1, g2, by rw [show j + S T j = j + d + 1 by omega]; exact hI,
      fun h => by rw [g3 53 (by omega)]; exact h53 h, ?_, g4, g5, g6, g7, g8⟩
    intro x x1 x2 x3 x4 x5 x6 x7 x8; exact g3 x x3
  | succ r ih =>
    intro d b bs s hr hpc hh hC h46 h74 h52 h54 h53 hI hM hcnt
    set k := j + d + 1 with hkdef
    have hkN : k < size T := by omega
    have hk46 : s.core.ptrs 46 + 1 = (k : ℤ) := by rw [h46, hkdef]; push_cast; ring
    have hke : (k : ℤ) < ((j + S T j : ℕ) : ℤ) := by push_cast; omega
    by_cases hu : unc T R k
    · -- unmarked: a candidate
      have hm : s.integerMemory (fa A 3 k) = 0 := by rw [hM k hkN, if_pos hu]
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10⟩ :=
        scan_pre Q off hE A _ _ k s hpc hh hC hk46 h74 hke hm (hcnt k (by omega) (by omega))
      set s1 := run Q s detTape 10 with hs1
      obtain ⟨t2, ht2, p1, p2, p3, p4, p5, p6, p7, p8, p9, p10⟩ :=
        scan_post Q off hE _ _ s1 g1 g2 (by rw [g5 52 (by omega) (by omega) (by omega) (by omega)
          (by omega), h52]) g4
      set s2 := run Q s1 detTape t2 with hs2
      have hck : cand T R j k := ⟨by omega, by omega, hu⟩
      have hsk := score_cast T R j k hj (by omega) (by omega)
      rw [hsk, g5 54 (by omega) (by omega) (by omega) (by omega) (by omega), h54] at p3 p4
      rw [g3, g5 53 (by omega) (by omega) (by omega) (by omega) (by omega)] at p4
      have hC2 : Consts s2 A := consts_of hC (fun x hx => by
        rw [p5 x (by omega) (by omega) (by omega) (by omega), g5 x (by omega) (by omega) (by omega)
          (by omega) (by omega)])
      have hfr : ∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 53 → x ≠ 54 → x ≠ 56 → x ≠ 57 → x ≠ 72 →
          s2.core.ptrs x = s.core.ptrs x := by
        intro x x1 x2 x3 x4 x5 x6 x7 x8
        rw [p5 x x4 x5 x6 x7, g5 x x1 x2 x3 x6 x8]
      have hM2 : Marks A T R s2 := marks_of hM (fun k' _ => by rw [p8, g8])
      have hcnt2 : ∀ k', j ≤ k' → k' < j + S T j → s2.integerMemory (fa A 4 k') = cntI T R k' := by
        intro k' k1 k2; rw [p8, g8]; exact hcnt k' k1 k2
      have h46' : s2.core.ptrs 46 = ((j + (d + 1) : ℕ) : ℤ) := by
        rw [p5 46 (by omega) (by omega) (by omega) (by omega), g3, hkdef]; push_cast; ring
      have h74' : s2.core.ptrs 74 = ((j + S T j : ℕ) : ℤ) := by rw [hfr 74 (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h74]
      have h52' : s2.core.ptrs 52 = (cntI T R j : ℤ) := by rw [hfr 52 (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h52]
      by_cases hlt : score T R j k < bs
      · have hlt' : (score T R j k : ℤ) < (bs : ℤ) := by exact_mod_cast hlt
        rw [if_pos hlt'] at p3 p4
        have hI' := sinv_take (cand T R j) (score T R j) (cntI T R j + 1) (j + 1) k b bs hI (by omega)
          hsc hck hlt
        obtain ⟨t3, b', bs', ht3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
          ih (d + 1) k (score T R j k) s2 (by omega) p1 p2 hC2 h46' h74' h52' p3 (fun _ => p4)
            (by rw [show j + (d + 1) + 1 = k + 1 by omega]; exact hI') hM2 hcnt2
        refine ⟨10 + t2 + t3, b', bs', by omega, ?_⟩
        rw [show 10 + t2 + t3 = 10 + (t2 + t3) by ring, run_add, run_add, cellsWritten_add,
          cellsWritten_add, ← hs1, ← hs2, g10, p10, q10]
        refine ⟨q1, q2, q3, q4, fun x x1 x2 x3 x4 x5 x6 x7 x8 => by
          rw [q5 x x1 x2 x3 x4 x5 x6 x7 x8, hfr x x1 x2 x3 x4 x5 x6 x7 x8], by rw [q6, p6, g6],
          by rw [q7, p7, g7], by rw [q8, p8, g8], by rw [q9, p9, g9]; ring, by simp⟩
      · have hge : (bs : ℤ) ≤ (score T R j k : ℤ) := by exact_mod_cast Nat.le_of_not_lt hlt
        rw [if_neg (by omega)] at p3 p4
        have hI' := sinv_skip (cand T R j) (score T R j) (cntI T R j + 1) (j + 1) k b bs hI (by omega)
          hsc (Or.inr (Nat.le_of_not_lt hlt))
        obtain ⟨t3, b', bs', ht3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
          ih (d + 1) b bs s2 (by omega) p1 p2 hC2 h46' h74' h52' p3
            (fun h => by rw [p4]; exact h53 h)
            (by rw [show j + (d + 1) + 1 = k + 1 by omega]; exact hI') hM2 hcnt2
        refine ⟨10 + t2 + t3, b', bs', by omega, ?_⟩
        rw [show 10 + t2 + t3 = 10 + (t2 + t3) by ring, run_add, run_add, cellsWritten_add,
          cellsWritten_add, ← hs1, ← hs2, g10, p10, q10]
        refine ⟨q1, q2, q3, q4, fun x x1 x2 x3 x4 x5 x6 x7 x8 => by
          rw [q5 x x1 x2 x3 x4 x5 x6 x7 x8, hfr x x1 x2 x3 x4 x5 x6 x7 x8], by rw [q6, p6, g6],
          by rw [q7, p7, g7], by rw [q8, p8, g8], by rw [q9, p9, g9]; ring, by simp⟩
    · -- marked: skip
      have hm : s.integerMemory (fa A 3 k) = 1 := by rw [hM k hkN, if_neg hu]
      obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
        scan_marked Q off hE A _ k s hpc hh hC hk46 h74 hke hm
      set s1 := run Q s detTape 9 with hs1
      have hfr : ∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 72 → s1.core.ptrs x = s.core.ptrs x := g4
      have hC1 : Consts s1 A := consts_of hC (fun x hx => hfr x (by omega) (by omega) (by omega)
        (by omega))
      have hI' := sinv_skip (cand T R j) (score T R j) (cntI T R j + 1) (j + 1) k b bs hI (by omega)
        hsc (Or.inl (fun h => hu h.2.2))
      obtain ⟨t3, b', bs', ht3, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
        ih (d + 1) b bs s1 (by omega) g1 g2 hC1 (by rw [g3, hkdef]; push_cast; ring)
          (by rw [hfr 74 (by omega) (by omega) (by omega) (by omega), h74])
          (by rw [hfr 52 (by omega) (by omega) (by omega) (by omega), h52])
          (by rw [hfr 54 (by omega) (by omega) (by omega) (by omega), h54])
          (fun h => by rw [hfr 53 (by omega) (by omega) (by omega) (by omega)]; exact h53 h)
          (by rw [show j + (d + 1) + 1 = k + 1 by omega]; exact hI')
          (marks_of hM (fun k' _ => by rw [g7])) (fun k' k1 k2 => by rw [g7]; exact hcnt k' k1 k2)
      refine ⟨9 + t3, b', bs', by omega, ?_⟩
      rw [run_add, cellsWritten_add, ← hs1, g9, q10]
      refine ⟨q1, q2, q3, q4, fun x x1 x2 x3 x4 x5 x6 x7 x8 => by
        rw [q5 x x1 x2 x3 x4 x5 x6 x7 x8, hfr x x1 x2 x3 x8], by rw [q6, g5], by rw [q7, g6],
        by rw [q8, g7], by rw [q9, g8]; ring, by simp⟩

end DetANN.HPIM.BB

-- ===== BB_Node =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- Offsets 153–175: the test node at `u` (`I[u] = 1`, `I[u+1] = v`, `I[u+2] = u + 4`), then the box
source address of record `b`. -/
lemma seg_node1 (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A u v a src : ℤ) (b : ℕ)
    (s : State) (hpc : s.core.pc = off + 153) (hh : s.halted = false) (hC : Consts s A)
    (h15 : s.core.ptrs 15 = u) (h16 : s.core.ptrs 16 = v) (h53 : s.core.ptrs 53 = b)
    (hA : A ≤ 0) (hu : 0 ≤ u) (ha : s.integerMemory (fa A 1 b) = a) (ha1 : a + 1 < 0)
    (hs : s.integerMemory (a + 1) = src) :
    (run Q s detTape 23).core.pc = off + 176 ∧ (run Q s detTape 23).halted = false ∧
      (run Q s detTape 23).core.ptrs 55 = u ∧ (run Q s detTape 23).core.ptrs 15 = u + 4 ∧
      (run Q s detTape 23).core.ptrs 44 = src ∧
      (run Q s detTape 23).core.ptrs 57 = s.core.ptrs 1 + s.core.ptrs 1 ∧
      (run Q s detTape 23).core.ptrs 46 = 0 ∧
      (run Q s detTape 23).integerMemory u = 1 ∧ (run Q s detTape 23).integerMemory (u + 1) = v ∧
      (run Q s detTape 23).integerMemory (u + 2) = u + 4 ∧
      (∀ z, z ≠ u → z ≠ u + 1 → z ≠ u + 2 → (run Q s detTape 23).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 46 → x ≠ 55 → x ≠ 56 → x ≠ 57 → x ≠ 72 →
        (run Q s detTape 23).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 23).core.regs = s.core.regs ∧ (run Q s detTape 23).core.mem = s.core.mem ∧
      (run Q s detTape 23).work = s.work + 23 ∧
      ∀ c ∈ cellsWritten Q s 23, c = (false, u) ∨ c = (false, u + 1) ∨ c = (false, u + 2) :=
  node_steps.2.2.2.2.2.2.1 Q off hE A u v a src b s hpc hh hC h15 h16 h53 hA hu ha ha1 hs

/-- One copy step (offsets 176–182). -/
lemma copy_step (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (q : ℤ) (s : State)
    (hpc : s.core.pc = off + 176) (hh : s.halted = false) (h46 : s.core.ptrs 46 = q)
    (hq : q < s.core.ptrs 57) :
    (run Q s detTape 7).core.pc = off + 176 ∧ (run Q s detTape 7).halted = false ∧
      (run Q s detTape 7).core.ptrs 46 = q + 1 ∧
      (∀ x, x ≠ 46 → x ≠ 58 → (run Q s detTape 7).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 40 → (run Q s detTape 7).core.regs x = s.core.regs x) ∧
      (run Q s detTape 7).core.mem =
        Function.update s.core.mem (s.core.ptrs 16 + q) (s.core.mem (s.core.ptrs 44 + q)) ∧
      (run Q s detTape 7).integerMemory = s.integerMemory ∧
      (run Q s detTape 7).work = s.work + 7 ∧
      ∀ c ∈ cellsWritten Q s 7, c = (true, s.core.ptrs 16 + q) :=
  node_steps.2.2.2.2.2.2.2.1 Q off hE q s hpc hh h46 hq

/-- **The box copy**: `mem[v + q] := mem[src + q]` for `q < 2m`, from a negative source. -/
lemma copy_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (v src : ℤ) (M : ℤ → ℝ) (mm : ℕ) :
    ∀ (c q : ℕ) (s : State), q + c = mm → s.core.pc = off + 176 → s.halted = false →
      s.core.ptrs 46 = q → s.core.ptrs 57 = mm → s.core.ptrs 16 = v → s.core.ptrs 44 = src →
      0 ≤ v → src + mm ≤ 0 →
      (∀ q' : ℕ, q' < q → s.core.mem (v + q') = M (src + q')) →
      (∀ z, (z < v ∨ v + q ≤ z) → s.core.mem z = M z) →
      ∃ t, t ≤ 7 * c + 1 ∧ (run Q s detTape t).core.pc = off + 183 ∧
        (run Q s detTape t).halted = false ∧
        (∀ q' : ℕ, q' < mm → (run Q s detTape t).core.mem (v + q') = M (src + q')) ∧
        (∀ z, (z < v ∨ v + mm ≤ z) → (run Q s detTape t).core.mem z = M z) ∧
        (∀ x, x ≠ 46 → x ≠ 58 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (∀ x, x ≠ 40 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
        (run Q s detTape t).integerMemory = s.integerMemory ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ w ∈ cellsWritten Q s t, w.1 = true ∧ v ≤ w.2 ∧ w.2 < v + mm := by
  intro c
  induction c with
  | zero =>
    intro q s hqc hpc hh h46 h57 h16 h44 hv hsrc hin hout
    refine ⟨1, by omega, ?_⟩
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh h46 h57 h16 h44 hin hout ⊢
    subst hh
    rw [hpc]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, fun q' hq' => hin q' (by omega), fun z hz => hout z (by omega), fun x _ _ => rfl,
      fun x _ => rfl, rfl, rfl, by simp⟩
  | succ c ih =>
    intro q s hqc hpc hh h46 h57 h16 h44 hv hsrc hin hout
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
      copy_step Q off hE q s hpc hh h46 (by rw [h57]; push_cast; omega)
    set s1 := run Q s detTape 7 with hs1
    rw [h16, h44] at g6; rw [h16] at g9
    have hrd : s.core.mem (src + q) = M (src + q) := hout _ (Or.inl (by omega))
    obtain ⟨t, ht, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
      ih (q + 1) s1 (by omega) g1 g2 (by rw [g3]; push_cast; ring)
        (by rw [g4 57 (by omega) (by omega), h57]) (by rw [g4 16 (by omega) (by omega), h16])
        (by rw [g4 44 (by omega) (by omega), h44]) hv hsrc
        (by
          intro q' hq'
          rw [g6, Function.update_apply]
          by_cases e : q' = q
          · subst e; rw [if_pos rfl, hrd]
          · rw [if_neg (by push_cast; omega)]; exact hin q' (by omega))
        (by
          intro z hz
          rw [g6, Function.update_apply, if_neg (by push_cast at hz ⊢; omega)]
          exact hout z (by push_cast at hz; omega))
    refine ⟨7 + t, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, q3, q4, fun x x1 x2 => by rw [q5 x x1 x2, g4 x x1 x2],
      fun x x1 => by rw [q6 x x1, g5 x x1], by rw [q7, g7], by rw [q8, g8]; ring, ?_⟩
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [g9 w hw]; simp; omega
    · exact q9 w hw

/-- Offsets 183–198: `v += 2m`; push the frame `(j, b, u, f)`; `f := f − 1`, `j := b`; `CALL`. -/
lemma seg_push (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (sp : ℤ) (s : State)
    (hpc : s.core.pc = off + 183) (hh : s.halted = false) (h47 : s.core.ptrs 47 = sp) :
    (run Q s detTape 16).core.pc = off + 87 ∧ (run Q s detTape 16).halted = false ∧
      (run Q s detTape 16).core.ptrs 16 = s.core.ptrs 16 + s.core.ptrs 57 ∧
      (run Q s detTape 16).core.ptrs 47 = sp - 4 ∧
      (run Q s detTape 16).core.ptrs 49 = s.core.ptrs 49 - 1 ∧
      (run Q s detTape 16).core.ptrs 50 = s.core.ptrs 53 ∧
      (run Q s detTape 16).integerMemory (sp - 4) = s.core.ptrs 50 ∧
      (run Q s detTape 16).integerMemory (sp - 3) = s.core.ptrs 53 ∧
      (run Q s detTape 16).integerMemory (sp - 2) = s.core.ptrs 55 ∧
      (run Q s detTape 16).integerMemory (sp - 1) = s.core.ptrs 49 ∧
      (∀ z, (z < sp - 4 ∨ sp ≤ z) → (run Q s detTape 16).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 16 → x ≠ 44 → x ≠ 47 → x ≠ 49 → x ≠ 50 → (run Q s detTape 16).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 16).core.regs = s.core.regs ∧ (run Q s detTape 16).core.mem = s.core.mem ∧
      (run Q s detTape 16).work = s.work + 16 ∧
      ∀ c ∈ cellsWritten Q s 16, c.1 = false ∧ sp - 4 ≤ c.2 ∧ c.2 < sp :=
  node_steps.2.2.2.2.2.2.2.2.1 Q off hE sp s hpc hh h47

/-- `RET` with a frame on the stack (offsets 218–243): pop `(j, b, u, f)`, `I[u+3] := ptr15`, set up
the marking of `[b, b + sz b)`. -/
lemma seg_ret (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A sp base j b u f Sb : ℤ)
    (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hC : Consts s A)
    (h47 : s.core.ptrs 47 = sp) (h48 : s.core.ptrs 48 = base) (hsp : sp < base) (hsp0 : sp + 4 ≤ 0)
    (hu : 0 ≤ u) (hA : A ≤ 0)
    (f0 : s.integerMemory sp = j) (f1 : s.integerMemory (sp + 1) = b)
    (f2 : s.integerMemory (sp + 2) = u) (f3 : s.integerMemory (sp + 3) = f)
    (hb : 0 ≤ b) (hSb : s.integerMemory (A - 3 - 5 * b) = Sb) :
    (run Q s detTape 26).core.pc = off + 244 ∧ (run Q s detTape 26).halted = false ∧
      (run Q s detTape 26).core.ptrs 50 = j ∧ (run Q s detTape 26).core.ptrs 53 = b ∧
      (run Q s detTape 26).core.ptrs 55 = u ∧ (run Q s detTape 26).core.ptrs 49 = f ∧
      (run Q s detTape 26).core.ptrs 47 = sp + 4 ∧ (run Q s detTape 26).core.ptrs 74 = b + Sb ∧
      (run Q s detTape 26).core.ptrs 46 = b ∧ (run Q s detTape 26).core.ptrs 56 = 1 ∧
      (run Q s detTape 26).integerMemory (u + 3) = s.core.ptrs 15 ∧
      (∀ z, z ≠ u + 3 → (run Q s detTape 26).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 51 → x ≠ 53 → x ≠ 55 → x ≠ 56 → x ≠ 72 →
        x ≠ 74 → (run Q s detTape 26).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 26).core.regs = s.core.regs ∧ (run Q s detTape 26).core.mem = s.core.mem ∧
      (run Q s detTape 26).work = s.work + 26 ∧
      ∀ c ∈ cellsWritten Q s 26, c = (false, u + 3) :=
  node_steps.2.2.2.2.2.2.2.2.2.1 Q off hE A sp base j b u f Sb s hpc hh hC h47 h48 hsp hsp0 hu hA f0 f1 f2 f3 hb hSb

/-- One marking step (offsets 244–251): `mk[i] := 1`. -/
lemma mark_step (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (i : ℕ) (s : State)
    (hpc : s.core.pc = off + 244) (hh : s.halted = false) (hC : Consts s A)
    (h46 : s.core.ptrs 46 = i) (h56 : s.core.ptrs 56 = 1) (hie : (i : ℤ) < s.core.ptrs 74) :
    (run Q s detTape 8).core.pc = off + 244 ∧ (run Q s detTape 8).halted = false ∧
      (run Q s detTape 8).core.ptrs 46 = ((i + 1 : ℕ) : ℤ) ∧
      (run Q s detTape 8).integerMemory = Function.update s.integerMemory (fa A 3 i) 1 ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 72 → (run Q s detTape 8).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 8).core.regs = s.core.regs ∧ (run Q s detTape 8).core.mem = s.core.mem ∧
      (run Q s detTape 8).work = s.work + 8 ∧
      ∀ c ∈ cellsWritten Q s 8, c = (false, fa A 3 i) :=
  node_steps.2.2.2.2.2.2.2.2.2.2.1 Q off hE A i s hpc hh hC h46 h56 hie

/-- **Marking** `[i, e)`, then `f := f − 1` and `CALL` (offsets 244–253). -/
lemma mark_loop (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (e : ℕ) :
    ∀ (c i : ℕ) (s : State), i + c = e → s.core.pc = off + 244 → s.halted = false → Consts s A →
      s.core.ptrs 46 = i → s.core.ptrs 56 = 1 → s.core.ptrs 74 = e →
      ∃ t, t ≤ 8 * c + 3 ∧ (run Q s detTape t).core.pc = off + 87 ∧ (run Q s detTape t).halted = false ∧
        (∀ k : ℕ, i ≤ k → k < e → (run Q s detTape t).integerMemory (fa A 3 k) = 1) ∧
        (∀ z, (∀ k : ℕ, i ≤ k → k < e → z ≠ fa A 3 k) →
          (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
        (run Q s detTape t).core.ptrs 49 = s.core.ptrs 49 - 1 ∧
        (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 49 → x ≠ 72 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
        (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
        (run Q s detTape t).work = s.work + t ∧
        ∀ w ∈ cellsWritten Q s t, ∃ k : ℕ, i ≤ k ∧ k < e ∧ w = (false, fa A 3 k) := by
  intro c
  induction c with
  | zero =>
    intro i s hie hpc hh hC h46 h56 h74
    refine ⟨3, by omega, ?_⟩
    obtain ⟨c13, c60, c61, c62, c63, c64, c69, c70⟩ := hC
    obtain ⟨⟨pc, regs, ptrs, mem⟩, im, cur, hlt, w⟩ := s
    simp only at hpc hh c13 c60 c61 c62 c63 c64 c69 c70 h46 h56 h74 ⊢
    subst hh
    rw [hpc]
    (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg]); (rw [run_exec_at hE rfl rfl rfl, cw_exec_at hE rfl rfl rfl]; simp (config := {decide := true}) only [exec, coreExec, wcell, Nat.add_assoc, Nat.reduceAdd, Function.update_apply, if_true, if_false, le_refl]; try simp (disch := omega) only [if_pos, if_neg])
    rw [run_zero, cw_zero]
    refine ⟨rfl, rfl, fun k k1 k2 => by omega, fun z _ => rfl, by simp, ?_, rfl, rfl, rfl, by simp⟩
    intro x x1 x2 x3 x4
    simp (disch := omega) only [Function.update_apply, if_pos, if_neg]
  | succ c ih =>
    intro i s hie hpc hh hC h46 h56 h74
    obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9⟩ :=
      mark_step Q off hE A i s hpc hh hC h46 h56 (by rw [h74]; push_cast; omega)
    set s1 := run Q s detTape 8 with hs1
    have hC1 : Consts s1 A := consts_of hC (fun x hx => g5 x (by omega) (by omega) (by omega))
    obtain ⟨t, ht, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
      ih (i + 1) s1 (by omega) g1 g2 hC1 g3 (by rw [g5 56 (by omega) (by omega) (by omega), h56])
        (by rw [g5 74 (by omega) (by omega) (by omega), h74])
    refine ⟨8 + t, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨q1, q2, ?_, ?_, by rw [q5, g5 49 (by omega) (by omega) (by omega)], ?_, by rw [q7, g6],
      by rw [q8, g7], by rw [q9, g8]; ring, ?_⟩
    · intro k k1 k2
      rcases Nat.eq_or_lt_of_le k1 with rfl | k1
      · rw [q4 _ (fun k' k1' _ => by unfold fa; omega), g4, Function.update_apply, if_pos rfl]
      · exact q3 k k1 k2
    · intro z hz
      rw [q4 z (fun k' k1 k2 => hz k' (by omega) k2), g4, Function.update_apply,
        if_neg (hz i le_rfl (by omega))]
    · intro x x1 x2 x3 x4
      rw [q6 x x1 x2 x3 x4, g5 x x1 x2 x4]
    · intro w hw
      rcases Finset.mem_union.1 hw with hw | hw
      · exact ⟨i, le_rfl, by omega, g9 w hw⟩
      · obtain ⟨k, k1, k2, e⟩ := q10 w hw; exact ⟨k, by omega, k2, e⟩

/-- `RET` with an empty stack: the block ends. -/
lemma seg_end (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State)
    (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hsp : s.core.ptrs 48 ≤ s.core.ptrs 47) :
    (run Q s detTape 1).core.pc = off + 254 ∧ (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core = { s.core with pc := off + 254 } ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅ :=
  node_steps.2.2.2.2.2.2.2.2.2.2.2 Q off hE s hpc hh hsp

end DetANN.HPIM.BB

-- ===== BB_Parts =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

lemma cands_nonempty (T : BSP m) (R : Finset (List Bool)) (j : ℕ) (h : 2 ≤ cntI T R j) :
    (candsI T R j).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hsub : (Finset.Ico j (j + S T j)).filter (unc T R) ⊆ {j} := by
    intro k hk
    simp only [Finset.mem_filter, Finset.mem_Ico] at hk
    rcases Nat.eq_or_lt_of_le hk.1.1 with e | e
    · simp [e]
    · exfalso
      have hk' : k ∈ candsI T R j := by
        simp only [candsI, Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨e, hk.1.2⟩, hk.2⟩
      rw [hne] at hk'; simp at hk'
  have := Finset.card_le_card hsub
  unfold cntI at h; simp only [Finset.card_singleton] at this; omega

lemma cand_filter (T : BSP m) (R : Finset (List Bool)) (j : ℕ) :
    (Finset.Ico (j + 1) (j + S T j)).filter (cand T R j) = candsI T R j := by
  unfold candsI
  apply Finset.filter_congr
  intro k hk
  simp only [Finset.mem_Ico] at hk
  unfold cand
  exact ⟨fun h => h.2.2, fun h => ⟨by omega, hk.2, h⟩⟩

lemma cnt_pos (T : BSP m) (R : Finset (List Bool)) (j : ℕ) (hu : unc T R j) : 1 ≤ cntI T R j := by
  unfold cntI
  apply Finset.card_pos.2
  exact ⟨j, by simp only [Finset.mem_filter, Finset.mem_Ico]; exact ⟨⟨le_rfl, by have := size_pos (U T j); unfold S; omega⟩, hu⟩⟩

set_option maxHeartbeats 1000000 in
/-- From `CALL` (fuel `≥ 1`) through the count pass to `CNTDONE`. -/
lemma head_cnt (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (T : BSP m) (R : Finset (List Bool)) (j : ℕ) (hj : j < size T) (s : State)
    (hpc : s.core.pc = off + 87) (hh : s.halted = false) (hC : Consts s A) (h49 : 1 ≤ s.core.ptrs 49)
    (h50 : s.core.ptrs 50 = j) (hR : Recs s0 ilo ihi rlo rhi A T s) (hM : Marks A T R s) :
    ∃ t, t ≤ 33 * S T j + 8 ∧ (run Q s detTape t).core.pc = off + 127 ∧
      (run Q s detTape t).halted = false ∧ Consts (run Q s detTape t) A ∧
      (run Q s detTape t).core.ptrs 67 = 5 * (j : ℤ) ∧ (run Q s detTape t).core.ptrs 51 = S T j ∧
      (∀ k, j ≤ k → k < j + S T j → (run Q s detTape t).integerMemory (fa A 4 k) = cntI T R k) ∧
      (∀ z, (∀ k : ℕ, j ≤ k → k < j + S T j → z ≠ fa A 4 k) →
        (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 51 → x ≠ 56 → x ≠ 57 → x ≠ 58 → x ≠ 67 → x ≠ 72 → x ≠ 73 →
        (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ w ∈ cellsWritten Q s t, ∃ k : ℕ, j ≤ k ∧ k < j + S T j ∧ w = (false, fa A 4 k) := by
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ := seg_head Q off hE A j s hpc hh hC h49 h50
  set s1 := run Q s detTape 7 with hs1
  have hSj := (hR j hj).2.2
  rw [hSj] at g3 g4
  have hC1 : Consts s1 A := consts_of hC (fun x hx => g6 x (by omega) (by omega) (by omega) (by omega))
  have hR1 : Recs s0 ilo ihi rlo rhi A T s1 := recs_of hR (fun k _ f _ _ => by rw [g9])
  have hM1 : Marks A T R s1 := marks_of hM (fun k _ => by rw [g9])
  obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    cnt_loop Q off hE A s0 ilo ihi rlo rhi T R j hj (S T j) s1 le_rfl g1 g2 hC1 (by rw [g4]; push_cast; ring)
      (by rw [g6 50 (by omega) (by omega) (by omega) (by omega), h50]) hR1 hM1
      (fun k k1 k2 => by omega)
  refine ⟨7 + t2, by omega, ?_⟩
  rw [run_add, cellsWritten_add, ← hs1, g11]
  have hC2 := consts_of hC1 (fun x hx => q5 x (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega))
  refine ⟨q1, q2, hC2, ?_, ?_, q3, fun z hz => by rw [q4 z hz, g9], ?_, by rw [q6, g7], by rw [q7, g8],
    by rw [q8, g10]; ring, by simpa using q9⟩
  · rw [q5 67 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g5]
  · rw [q5 51 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), g3]
  · intro x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
    rw [q5 x x1 x2 x3 x5 x6 x7 x9 x10, g6 x x1 x3 x4 x8]

/-- `CNTDONE` with `total ≤ 1`: the leaf `(U T j).ans` at `u`. -/
lemma leaf_part (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (T : BSP m) (R : Finset (List Bool)) (j : ℕ) (hj : j < size T) (u v : ℤ)
    (s : State) (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A)
    (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h15 : s.core.ptrs 15 = u) (hu : 0 ≤ u) (hA : A ≤ ilo) (hA0 : A ≤ 0)
    (hR : Recs s0 ilo ihi rlo rhi A T s)
    (hagI : ∀ z, ilo ≤ z → z < ihi → s.integerMemory z = s0.integerMemory z)
    (hcnt : s.integerMemory (fa A 4 j) = cntI T R j) (htot : cntI T R j ≤ 1) :
    ∃ t, t ≤ 20 ∧ (run Q s detTape t).core.pc = off + 218 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 15 = u + 2 ∧
      Good (run Q s detTape t) u v (u + 2) v (BoxTree.leaf (m := m) (U T j).ans) ∧
      (∀ z, z ≠ u → z ≠ u + 1 → (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 15 → x ≠ 44 → x ≠ 45 → x ≠ 52 → x ≠ 56 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, u) ∨ c = (false, u + 1) := by
  obtain ⟨k0, hB, _⟩ := hR j hj
  have hav : (s.integerMemory (fa A 0 j) = 0 ∧
      s.integerMemory (s.integerMemory (fa A 1 j) + 2) = enc (U T j).ans) ∨
      (s.integerMemory (fa A 0 j) = 1 ∧ enc (U T j).ans = 0) := by
    rcases kindOf_cut_or (U T j) with ⟨hk, lo, hi, a, hU⟩ | ⟨hk, lo, hi, l, r, hU⟩
    · left
      refine ⟨by rw [k0, hk], ?_⟩
      rw [hU] at hB ⊢
      obtain ⟨b1, b2, -⟩ := bsp_info hB
      rw [hagI _ (by omega) (by omega), bsp_ans hB]; rfl
    · right
      refine ⟨by rw [k0, hk], ?_⟩
      rw [hU]; rfl
  obtain ⟨t, ht, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ :=
    seg_leafout Q off hE A u _ _ j s hpc hh hC h67 h15 hcnt (by exact_mod_cast htot)
      (by omega) hav
  exact ⟨t, ht, g1, g2, g3, good_leaf _ g4 g5, g6, g7, g8, g9, g10, g11⟩

set_option maxHeartbeats 1000000 in
/-- `CNTDONE` with `total ≥ 2`: the scan finds the centroid `b`. -/
lemma scan_part (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (T : BSP m)
    (R : Finset (List Bool)) (j : ℕ) (hj : j < size T) (s : State)
    (hpc : s.core.pc = off + 127) (hh : s.halted = false) (hC : Consts s A)
    (h67 : s.core.ptrs 67 = 5 * (j : ℤ)) (h50 : s.core.ptrs 50 = j) (h51 : s.core.ptrs 51 = S T j)
    (hM : Marks A T R s)
    (hcnt : ∀ k, j ≤ k → k < j + S T j → s.integerMemory (fa A 4 k) = cntI T R k)
    (htot : 2 ≤ cntI T R j) :
    ∃ (t b : ℕ), t ≤ 17 * S T j + 10 ∧ (run Q s detTape t).core.pc = off + 153 ∧
      (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 53 = (b : ℤ) ∧
      b ∈ candsI T R j ∧ (∀ k ∈ candsI T R j, score T R j b ≤ score T R j k) ∧
      (∀ k ∈ candsI T R j, score T R j k = score T R j b → b ≤ k) ∧
      (∀ x, x ≠ 44 → x ≠ 45 → x ≠ 46 → x ≠ 52 → x ≠ 53 → x ≠ 54 → x ≠ 56 → x ≠ 57 → x ≠ 72 → x ≠ 74 →
        (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).integerMemory = s.integerMemory ∧
      (run Q s detTape t).work = s.work + t ∧ cellsWritten Q s t = ∅ := by
  have hS1 : 1 ≤ S T j := size_pos _
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
    seg_scan0 Q off hE A _ j s hpc hh hC h67 h50 (hcnt j le_rfl (by omega)) (by exact_mod_cast htot)
  set s1 := run Q s detTape 8 with hs1
  have hC1 : Consts s1 A := consts_of hC (fun x hx => g7 x (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega))
  obtain ⟨t2, b', bs', ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
    scan_loop Q off hE A T R j hj (S T j - 1) 0 0 (cntI T R j + 1) s1 (by omega) g1 g2 hC1
      (by rw [g5]; simp) (by rw [g6, h51]; push_cast; ring) g3 (by rw [g4]; push_cast; ring)
      (fun h => by omega) (sinv_start _ _ _ _ _) (marks_of hM (fun k _ => by rw [g10]))
      (fun k k1 k2 => by rw [g10]; exact hcnt k k1 k2)
  have hne := cands_nonempty T R j htot
  rw [← cand_filter] at hne
  obtain ⟨e1, e2, e3⟩ := sinv_end (cand T R j) (score T R j) (cntI T R j + 1) (j + 1) (j + S T j) b' bs'
    q3 (score_lt T R j hj) hne
  have hbs : bs' < cntI T R j + 1 := by
    rcases q3 with ⟨_, h⟩ | ⟨_, _, hc, hb, _⟩
    · obtain ⟨k, hk⟩ := hne
      simp only [Finset.mem_filter, Finset.mem_Ico] at hk
      exact absurd hk.2 (h k hk.1.1 hk.1.2)
    · rw [hb]; exact score_lt T R j hj b' hc
  rw [cand_filter] at e1 e2 e3
  refine ⟨8 + t2, b', by omega, ?_⟩
  rw [run_add, cellsWritten_add, ← hs1, g12, q10]
  refine ⟨q1, q2, q4 hbs, e1, e2, e3, ?_, by rw [q6, g8], by rw [q7, g9], by rw [q8, g10],
    by rw [q9, g11]; ring, by simp⟩
  intro x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10
  rw [q5 x x1 x2 x3 x5 x6 x7 x8 x9, g7 x x1 x3 x4 x6 x7 x10]

end DetANN.HPIM.BB

-- ===== BB_Parts2 =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

set_option maxHeartbeats 1000000 in
/-- From `SCANDONE` with centroid `b`: the test node at `u`, its box at `v`, the frame at `sp − 4`,
then `CALL` for the *yes* subtree. -/
lemma node_part (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (T : BSP m) (b : ℕ) (hb : b < size T) (u v sp : ℤ) (s : State)
    (hpc : s.core.pc = off + 153) (hh : s.halted = false) (hC : Consts s A)
    (h53 : s.core.ptrs 53 = b) (h15 : s.core.ptrs 15 = u) (h16 : s.core.ptrs 16 = v)
    (h1 : s.core.ptrs 1 = m) (h47 : s.core.ptrs 47 = sp) (hsp0 : sp ≤ 0) (hu : 0 ≤ u) (hv : 0 ≤ v) (hA0 : A ≤ 0)
    (hihi : ihi ≤ 0) (hrhi : rhi ≤ 0) (hR : Recs s0 ilo ihi rlo rhi A T s)
    (hagI : ∀ z, ilo ≤ z → z < ihi → s.integerMemory z = s0.integerMemory z)
    (hagM : ∀ z, rlo ≤ z → z < rhi → s.core.mem z = s0.core.mem z) :
    ∃ t, t ≤ 14 * m + 41 ∧ (run Q s detTape t).core.pc = off + 87 ∧ (run Q s detTape t).halted = false ∧
      (run Q s detTape t).core.ptrs 15 = u + 4 ∧ (run Q s detTape t).core.ptrs 16 = v + 2 * m ∧
      (run Q s detTape t).core.ptrs 47 = sp - 4 ∧
      (run Q s detTape t).core.ptrs 49 = s.core.ptrs 49 - 1 ∧ (run Q s detTape t).core.ptrs 50 = b ∧
      (run Q s detTape t).integerMemory u = 1 ∧ (run Q s detTape t).integerMemory (u + 1) = v ∧
      (run Q s detTape t).integerMemory (u + 2) = u + 4 ∧
      (run Q s detTape t).integerMemory (sp - 4) = s.core.ptrs 50 ∧
      (run Q s detTape t).integerMemory (sp - 3) = b ∧
      (run Q s detTape t).integerMemory (sp - 2) = u ∧
      (run Q s detTape t).integerMemory (sp - 1) = s.core.ptrs 49 ∧
      (∀ jj : Fin m, (run Q s detTape t).core.mem (v + jj) = (U T b).box.1 jj) ∧
      (∀ jj : Fin m, (run Q s detTape t).core.mem (v + m + jj) = (U T b).box.2 jj) ∧
      (∀ z, z ≠ u → z ≠ u + 1 → z ≠ u + 2 → (z < sp - 4 ∨ sp ≤ z) →
        (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ z, (z < v ∨ v + 2 * m ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (∀ x, x ≠ 15 → x ≠ 16 → x ≠ 44 → x ≠ 46 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 55 → x ≠ 56 → x ≠ 57 →
        x ≠ 58 → x ≠ 72 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (∀ x, x ≠ 40 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, (c.1 = false ∧ (c.2 = u ∨ c.2 = u + 1 ∨ c.2 = u + 2 ∨
        (sp - 4 ≤ c.2 ∧ c.2 < sp))) ∨ (c.1 = true ∧ v ≤ c.2 ∧ c.2 < v + 2 * m) := by
  obtain ⟨-, hB, -⟩ := hR b hb
  set a := s.integerMemory (fa A 1 b) with ha
  obtain ⟨b1, b2, -, b4, b5, b6, b7⟩ := bsp_info hB
  have hsrc : s.integerMemory (a + 1) = s0.integerMemory (a + 1) := hagI _ (by omega) (by omega)
  set src := s.integerMemory (a + 1) with hsrcdef
  rw [← hsrc] at b4 b5 b6 b7
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16⟩ :=
    seg_node1 Q off hE A u v a src b s hpc hh hC h15 h16 h53 hA0 hu rfl (by omega) rfl
  set s1 := run Q s detTape 23 with hs1
  rw [h1] at g6
  obtain ⟨t2, ht2, c1, c2, c3, c4, c5, c6, c7, c8, c9⟩ :=
    copy_loop Q off hE v src s1.core.mem (2 * m) (2 * m) 0 s1 (by omega) g1 g2 (by rw [g7]; simp)
      (by rw [g6]; push_cast; ring) (by rw [g12 16 (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), h16]) g5 hv (by push_cast; omega) (fun q' hq' => by omega) (fun z _ => rfl)
  set s2 := run Q s1 detTape t2 with hs2
  obtain ⟨p1, p2, p3, p4, p5, p6, p7, p8, p9, p10, p11, p12, p13, p14, p15, p16⟩ :=
    seg_push Q off hE sp s2 c1 c2 (by rw [c5 47 (by omega) (by omega), g12 47 (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), h47])
  set s3 := run Q s2 detTape 16 with hs3
  have r16 : s2.core.ptrs 16 = v := by rw [c5 16 (by omega) (by omega), g12 16 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega), h16]
  have r57 : s2.core.ptrs 57 = 2 * m := by rw [c5 57 (by omega) (by omega), g6]; ring
  have r50 : s2.core.ptrs 50 = s.core.ptrs 50 := by rw [c5 50 (by omega) (by omega), g12 50 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have r53 : s2.core.ptrs 53 = b := by rw [c5 53 (by omega) (by omega), g12 53 (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega), h53]
  have r55 : s2.core.ptrs 55 = u := by rw [c5 55 (by omega) (by omega), g3]
  have r49 : s2.core.ptrs 49 = s.core.ptrs 49 := by rw [c5 49 (by omega) (by omega), g12 49 (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)]
  have r15 : s2.core.ptrs 15 = u + 4 := by rw [c5 15 (by omega) (by omega), g4]
  -- the reals of the box
  have hbox : ∀ q' : ℕ, q' < 2 * m → s3.core.mem (v + q') = s0.core.mem (src + q') := by
    intro q' hq'
    rw [p14, c3 q' hq', g14, hagM _ (by omega) (by omega)]
  refine ⟨23 + t2 + 16, by omega, ?_⟩
  have RR : run Q s detTape (23 + t2 + 16) = s3 := by rw [hs3, hs2, hs1]; simp only [← run_add]
  have CW : cellsWritten Q s (23 + t2 + 16) =
      cellsWritten Q s 23 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 16 := by
    rw [hs2, hs1]; simp only [cellsWritten_add, ← run_add]
  rw [RR, CW]
  have hi1 : ∀ z, (z < sp - 4 ∨ sp ≤ z) → s3.integerMemory z = s1.integerMemory z := by
    intro z hz; rw [p11 z hz, c7]
  refine ⟨p1, p2, by rw [p12 15 (by omega) (by omega) (by omega) (by omega) (by omega), r15], by rw [p3, r16, r57], p4, by rw [p5, r49], by rw [p6, r53], ?_, ?_, ?_,
    by rw [p7, r50], by rw [p8, r53], by rw [p9, r55], by rw [p10, r49], ?_, ?_, ?_, ?_, ?_,
    fun x hx => by rw [p13, c6 x hx, g13], by rw [p15, c8, g15]; ring, ?_⟩
  · rw [hi1 u (by omega), g8]
  · rw [hi1 (u + 1) (by omega), g9]
  · rw [hi1 (u + 2) (by omega), g10]
  · intro jj; have := jj.isLt
    rw [hbox jj (by omega)]; exact b6 jj
  · intro jj; have := jj.isLt
    have e := hbox (m + jj) (by omega)
    push_cast at e; rw [← add_assoc] at e; rw [e, ← add_assoc]; exact b7 jj
  · intro z z1 z2 z3 z4
    rw [hi1 z z4, g11 z z1 z2 z3]
  · intro z hz
    rw [p14, c4 z (by push_cast; omega), g14]
  · intro x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12
    rw [p12 x x2 x3 x5 x6 x7, c5 x x4 x11, g12 x x1 x3 x4 x8 x9 x10 x12]
  · intro c hc
    simp only [Finset.mem_union] at hc
    rcases hc with (hc | hc) | hc
    · left
      rcases g16 c hc with rfl | rfl | rfl <;> simp
    · right; obtain ⟨e1, e2, e3⟩ := c9 c hc; push_cast at e3; exact ⟨e1, e2, e3⟩
    · left; obtain ⟨e1, e2, e3⟩ := p16 c hc; exact ⟨e1, Or.inr (Or.inr (Or.inr ⟨e2, e3⟩))⟩

set_option maxHeartbeats 1000000 in
/-- `RET` after the *yes* subtree: pop `(j, b, u, f + 1)`, `I[u+3] := ptr15`, mark `[b, b + S b)`,
`f := f`, then `CALL` for the *no* subtree. -/
lemma ret_part (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (T : BSP m) (b : ℕ) (hb : b < size T) (j u : ℤ) (f : ℕ) (sp base : ℤ)
    (s : State) (hpc : s.core.pc = off + 218) (hh : s.halted = false) (hC : Consts s A)
    (h47 : s.core.ptrs 47 = sp - 4) (h48 : s.core.ptrs 48 = base) (hsp : sp ≤ base) (hsp0 : sp ≤ 0)
    (hu : 0 ≤ u) (hA0 : A ≤ 0)
    (f0 : s.integerMemory (sp - 4) = j) (f1 : s.integerMemory (sp - 3) = b)
    (f2 : s.integerMemory (sp - 2) = u) (f3 : s.integerMemory (sp - 1) = (f + 1 : ℕ))
    (hR : Recs s0 ilo ihi rlo rhi A T s) :
    ∃ t, t ≤ 8 * S T b + 29 ∧ (run Q s detTape t).core.pc = off + 87 ∧
      (run Q s detTape t).halted = false ∧ (run Q s detTape t).core.ptrs 50 = j ∧
      (run Q s detTape t).core.ptrs 49 = f ∧ (run Q s detTape t).core.ptrs 47 = sp ∧
      (run Q s detTape t).integerMemory (u + 3) = s.core.ptrs 15 ∧
      (∀ k : ℕ, b ≤ k → k < b + S T b → (run Q s detTape t).integerMemory (fa A 3 k) = 1) ∧
      (∀ z, z ≠ u + 3 → (∀ k : ℕ, b ≤ k → k < b + S T b → z ≠ fa A 3 k) →
        (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ x, x ≠ 44 → x ≠ 46 → x ≠ 47 → x ≠ 49 → x ≠ 50 → x ≠ 51 → x ≠ 53 → x ≠ 55 → x ≠ 56 → x ≠ 72 →
        x ≠ 74 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.regs = s.core.regs ∧ (run Q s detTape t).core.mem = s.core.mem ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t, c = (false, u + 3) ∨
        ∃ k : ℕ, b ≤ k ∧ k < b + S T b ∧ c = (false, fa A 3 k) := by
  have hSb := (hR b hb).2.2
  unfold fa at hSb
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17⟩ :=
    seg_ret Q off hE A (sp - 4) base j b u (f + 1 : ℕ) (S T b) s hpc hh hC h47 h48 (by omega) (by omega)
      hu hA0 f0 (by rw [show sp - 4 + 1 = sp - 3 by ring, f1])
      (by rw [show sp - 4 + 2 = sp - 2 by ring, f2]) (by rw [show sp - 4 + 3 = sp - 1 by ring, f3])
      (by omega) (by rw [← hSb]; congr 1; ring)
  set s1 := run Q s detTape 26 with hs1
  have hC1 : Consts s1 A := consts_of hC (fun x hx => g13 x (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
  obtain ⟨t2, ht2, q1, q2, q3, q4, q5, q6, q7, q8, q9, q10⟩ :=
    mark_loop Q off hE A (b + S T b) (S T b) b s1 rfl g1 g2 hC1 g9 g10 (by rw [g8]; push_cast; ring)
  refine ⟨26 + t2, by omega, ?_⟩
  rw [run_add, cellsWritten_add, ← hs1]
  refine ⟨q1, q2, by rw [q6 50 (by omega) (by omega) (by omega) (by omega), g3], ?_, ?_, ?_, q3, ?_, ?_,
    by rw [q7, g14], by rw [q8, g15], by rw [q9, g16]; ring, ?_⟩
  · rw [q5, g6]; push_cast; ring
  · rw [q6 47 (by omega) (by omega) (by omega) (by omega), g7]; ring
  · rw [q4 _ (fun k _ _ => by unfold fa; omega), g11]
  · intro z z1 z2; rw [q4 z z2, g12 z z1]
  · intro x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11
    rw [q6 x x1 x2 x4 x10, g13 x x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11]
  · intro c hc
    rcases Finset.mem_union.1 hc with hc | hc
    · left; exact g17 c hc
    · right; exact q10 c hc

end DetANN.HPIM.BB

-- ===== BB_Rec =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

/-- The work bound of one call (excluding its subcalls). -/
def W (N m : ℕ) : ℕ := 60 * N + 14 * m + 90

/-- The contract of `CALL` with fuel `f`: the output tree `balance T f (P T j) R` at `u`/`v`, the
stack, the marks outside the subtree of `j`, and the records kept. -/
def CallOK (Q : Program) (off : ℕ) (A : ℤ) (s0 : State) (ilo ihi rlo rhi : ℤ) (T : BSP m) (f : ℕ) :
    Prop :=
  ∀ (j : ℕ) (R : Finset (List Bool)) (s : State) (sp u v : ℤ),
    j < size T → unc T R j → s.core.pc = off + 87 → s.halted = false → Consts s A →
    s.core.ptrs 1 = m → s.core.ptrs 48 = A - 5 * (size T : ℤ) → s.core.ptrs 47 = sp →
    sp ≤ A - 5 * (size T : ℤ) → s.core.ptrs 49 = f → s.core.ptrs 50 = j →
    s.core.ptrs 15 = u → s.core.ptrs 16 = v → 0 ≤ u → 0 ≤ v →
    Recs s0 ilo ihi rlo rhi A T s → Marks A T R s →
    (∀ z, ilo ≤ z → z < ihi → s.integerMemory z = s0.integerMemory z) →
    (∀ z, rlo ≤ z → z < rhi → s.core.mem z = s0.core.mem z) →
    ∃ (t : ℕ) (u' v' : ℤ), t ≤ (2 * cntI T R j - 1) * W (size T) m ∧
      (run Q s detTape t).core.pc = off + 218 ∧ (run Q s detTape t).halted = false ∧
      Consts (run Q s detTape t) A ∧
      (∀ x, x < 40 → x ≠ 15 → x ≠ 16 → (run Q s detTape t).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape t).core.ptrs 48 = s.core.ptrs 48 ∧ (run Q s detTape t).core.ptrs 47 = sp ∧
      (run Q s detTape t).core.ptrs 15 = u' ∧ (run Q s detTape t).core.ptrs 16 = v' ∧
      u ≤ u' ∧ u' ≤ u + 4 * ((2 * cntI T R j - 1 : ℕ) : ℤ) ∧
      v ≤ v' ∧ v' ≤ v + 2 * m * ((2 * cntI T R j - 1 : ℕ) : ℤ) ∧
      Good (run Q s detTape t) u v u' v' (balance T f (P T j) R) ∧
      Recs s0 ilo ihi rlo rhi A T (run Q s detTape t) ∧
      (∀ k < size T, (k < j ∨ j + S T j ≤ k) →
        (run Q s detTape t).integerMemory (fa A 3 k) = s.integerMemory (fa A 3 k)) ∧
      (∀ z, (z < sp - 4 * f ∨ sp ≤ z) → (z < u ∨ u' ≤ z) →
        (∀ k < size T, z ≠ fa A 3 k ∧ z ≠ fa A 4 k) →
        (run Q s detTape t).integerMemory z = s.integerMemory z) ∧
      (∀ z, (z < v ∨ v' ≤ z) → (run Q s detTape t).core.mem z = s.core.mem z) ∧
      (∀ x, x ≠ 40 → (run Q s detTape t).core.regs x = s.core.regs x) ∧
      (run Q s detTape t).work = s.work + t ∧
      ∀ c ∈ cellsWritten Q s t,
        (c.1 = false ∧ ((A - 5 * (size T : ℤ) ≤ c.2 ∧ c.2 < A) ∨ (sp - 4 * f ≤ c.2 ∧ c.2 < sp) ∨
          (u ≤ c.2 ∧ c.2 < u'))) ∨ (c.1 = true ∧ v ≤ c.2 ∧ c.2 < v')

lemma recs_frame {s0 s s' : State} {ilo ihi rlo rhi A : ℤ} {T : BSP m}
    (h : Recs s0 ilo ihi rlo rhi A T s)
    (hf : ∀ z, A - 5 * (size T : ℤ) ≤ z → z < A → (∀ k < size T, z ≠ fa A 3 k ∧ z ≠ fa A 4 k) →
      s'.integerMemory z = s.integerMemory z) :
    Recs s0 ilo ihi rlo rhi A T s' :=
  recs_of h (fun k hk f f0 f1 => hf _ (by unfold fa; omega) (by unfold fa; omega)
    (fun k' _ => ⟨by unfold fa; omega, by unfold fa; omega⟩))

lemma call_zero (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (T : BSP m) (hA : A ≤ ilo) (hA0 : A ≤ 0) (hihi : ihi ≤ 0) :
    CallOK Q off A s0 ilo ihi rlo rhi T 0 := by
  intro j R s sp u v hj hu hpc hh hC h1 h48 h47 hsp h49 h50 h15 h16 hu0 hv0 hR hM hagI hagM
  have ha := cnt_pos T R j hu
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11⟩ :=
    seg_fuel0 Q off hE A u s hpc hh hC (by rw [h49]; rfl) h15
  have hW : 10 ≤ (2 * cntI T R j - 1) * W (size T) m := by
    have : 1 ≤ 2 * cntI T R j - 1 := by omega
    calc 10 ≤ W (size T) m := by unfold W; omega
      _ ≤ (2 * cntI T R j - 1) * W (size T) m := Nat.le_mul_of_pos_left _ this
  have hC' : Consts (run Q s detTape 10) A := consts_of hC (fun x hx => g7 x (by omega) (by omega) (by omega))
  refine ⟨10, u + 2, v, hW, g1, g2, hC', fun x x1 x2 x3 => g7 x x2 (by omega) (by omega),
    g7 48 (by omega) (by omega) (by omega), by rw [g7 47 (by omega) (by omega) (by omega), h47], g3,
    by rw [g7 16 (by omega) (by omega) (by omega), h16], by omega, by push_cast; omega, le_rfl,
    by have : (0 : ℤ) ≤ 2 * m * ((2 * cntI T R j - 1 : ℕ) : ℤ) := by positivity
       omega, ?_, ?_, ?_, ?_, fun z _ => by rw [g9], fun x _ => by rw [g8], g10, ?_⟩
  · show Good _ u v (u + 2) v (balance T 0 (P T j) R)
    rw [show balance T 0 (P T j) R = .leaf none from rfl]
    exact good_leaf none g4 (by rw [g5]; rfl)
  · exact recs_frame hR (fun z z1 z2 _ => g6 z (by omega) (by omega))
  · intro k hk _; exact g6 _ (by unfold fa; omega) (by unfold fa; omega)
  · intro z _ hz _; exact g6 z (by omega) (by omega)
  · intro c hc
    rcases g11 c hc with rfl | rfl
    · left; exact ⟨rfl, Or.inr (Or.inr ⟨le_rfl, by omega⟩)⟩
    · left; exact ⟨rfl, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩

end DetANN.HPIM.BB

-- ===== BB_Rec2 =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

variable {m : ℕ}

set_option maxHeartbeats 4000000 in
lemma call_succ (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (T : BSP m) (hA : A ≤ ilo) (hA0 : A ≤ 0) (hihi : ihi ≤ 0) (hrhi : rhi ≤ 0)
    (f : ℕ) (IH : CallOK Q off A s0 ilo ihi rlo rhi T f) :
    CallOK Q off A s0 ilo ihi rlo rhi T (f + 1) := by
  intro j R s sp u v hj hu hpc hh hC h1 h48 h47 hsp h49 h50 h15 h16 hu0 hv0 hR hM hagI hagM
  have ha := cnt_pos T R j hu
  have hbj := bound T j hj
  have hSj : 1 ≤ S T j := size_pos _
  -- 1. head and count
  obtain ⟨t1, ht1, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ :=
    head_cnt Q off hE A s0 ilo ihi rlo rhi T R j hj s hpc hh hC (by rw [h49]; push_cast; omega) h50 hR hM
  set s1 := run Q s detTape t1 with hs1
  have fr1 : ∀ x, (x < 40 ∨ x = 47 ∨ x = 48 ∨ x = 49 ∨ x = 50) → s1.core.ptrs x = s.core.ptrs x :=
    fun x hx => g8 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega)
  have im1 : ∀ z, (z < A - 5 * (size T : ℤ) ∨ A ≤ z ∨ (∀ k < size T, z ≠ fa A 4 k)) →
      s1.integerMemory z = s.integerMemory z := by
    intro z hz; apply g7; intro k k1 k2; unfold fa; rcases hz with hz | hz | hz
    · omega
    · omega
    · exact hz k (by omega)
  have hR1 : Recs s0 ilo ihi rlo rhi A T s1 :=
    recs_frame hR (fun z _ _ hz => im1 z (Or.inr (Or.inr (fun k hk => (hz k hk).2))))
  have hM1 : Marks A T R s1 := marks_of hM (fun k hk => im1 _ (Or.inr (Or.inr (fun k' _ => by
    unfold fa; omega))))
  have hagI1 : ∀ z, ilo ≤ z → z < ihi → s1.integerMemory z = s0.integerMemory z := by
    intro z z1 z2; rw [im1 z (Or.inr (Or.inl (by omega))), hagI z z1 z2]
  have hagM1 : ∀ z, rlo ≤ z → z < rhi → s1.core.mem z = s0.core.mem z := by
    intro z z1 z2; rw [g10, hagM z z1 z2]
  have hWge : 33 * S T j + 8 + 20 ≤ W (size T) m := by unfold W; omega
  have hWa : W (size T) m ≤ (2 * cntI T R j - 1) * W (size T) m :=
    Nat.le_mul_of_pos_left _ (by omega)
  by_cases htot : cntI T R j ≤ 1
  · -- the leaf
    obtain ⟨t2, ht2, l1, l2, l3, l4, l5, l6, l7, l8, l9, l10⟩ :=
      leaf_part Q off hE A s0 ilo ihi rlo rhi T R j hj u v s1 g1 g2 g3 g4
        (by rw [fr1 15 (by omega), h15]) hu0 hA hA0 hR1 hagI1 (g6 j le_rfl (by omega)) htot
    set s2 := run Q s1 detTape t2 with hs2
    have fr2 : ∀ x, (x < 40 ∨ x = 47 ∨ x = 48) → x ≠ 15 → s2.core.ptrs x = s.core.ptrs x := by
      intro x hx x15
      rw [l6 x x15 (by omega) (by omega) (by omega) (by omega), fr1 x (by omega)]
    refine ⟨t1 + t2, u + 2, v, by omega, ?_⟩
    rw [run_add, cellsWritten_add, ← hs1]
    refine ⟨l1, l2, consts_of g3 (fun x hx => l6 x (by omega) (by omega) (by omega) (by omega) (by omega)),
      fun x x1 x2 _ => fr2 x (Or.inl x1) x2, by rw [fr2 48 (by omega) (by omega)],
      by rw [fr2 47 (by omega) (by omega), h47], l3,
      by rw [l6 16 (by omega) (by omega) (by omega) (by omega) (by omega), fr1 16 (by omega), h16],
      by omega, by push_cast; omega, le_rfl,
      by have : (0 : ℤ) ≤ 2 * m * ((2 * cntI T R j - 1 : ℕ) : ℤ) := by positivity
         omega, ?_, ?_, ?_, ?_, fun z _ => by rw [l8, g10], fun x _ => by rw [l7, g9],
      by rw [l9, g11]; ring, ?_⟩
    · rw [balance_succ T R f j 0 hj (fun h => absurd h (by omega)), if_pos htot]; exact l4
    · exact recs_frame hR1 (fun z _ _ _ => l5 z (by omega) (by omega))
    · intro k hk _
      rw [l5 _ (by unfold fa; omega) (by unfold fa; omega)]
      exact im1 _ (Or.inr (Or.inr (fun k' _ => by unfold fa; omega)))
    · intro z _ hz hrec
      rw [l5 z (by omega) (by omega)]
      exact im1 z (Or.inr (Or.inr (fun k hk => (hrec k hk).2)))
    · intro c hc
      rcases Finset.mem_union.1 hc with hc | hc
      · obtain ⟨k, k1, k2, rfl⟩ := g12 c hc
        left; exact ⟨rfl, Or.inl ⟨by unfold fa; omega, by unfold fa; omega⟩⟩
      · rcases l10 c hc with rfl | rfl
        · left; exact ⟨rfl, Or.inr (Or.inr ⟨le_rfl, by omega⟩)⟩
        · left; exact ⟨rfl, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
  · -- the test node
    -- 2. scan
    obtain ⟨t2, b, ht2, k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, k12⟩ :=
      scan_part Q off hE A T R j hj s1 g1 g2 g3 g4 (by rw [fr1 50 (by omega), h50]) g5 hM1 g6
        (by omega)
    set s2 := run Q s1 detTape t2 with hs2
    have hbc : j < b ∧ b < j + S T j ∧ unc T R b := by
      simp only [candsI, Finset.mem_filter, Finset.mem_Ico] at k4; exact ⟨by omega, k4.1.2, k4.2⟩
    have hbN : b < size T := by omega
    have hbsub := sub_interval T j b hj hbc.1.le hbc.2.1
    have hSb : 1 ≤ S T b := size_pos _
    have fr2 : ∀ x, (x < 40 ∨ x = 47 ∨ x = 48 ∨ x = 49 ∨ x = 50) → s2.core.ptrs x = s.core.ptrs x := by
      intro x hx
      rw [k7 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega), fr1 x hx]
    have hC2 : Consts s2 A := consts_of g3 (fun x hx => k7 x (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    have hR2 : Recs s0 ilo ihi rlo rhi A T s2 := recs_of hR1 (fun k _ f _ _ => by rw [k10])
    have hagI2 : ∀ z, ilo ≤ z → z < ihi → s2.integerMemory z = s0.integerMemory z := by
      intro z z1 z2; rw [k10, hagI1 z z1 z2]
    have hagM2 : ∀ z, rlo ≤ z → z < rhi → s2.core.mem z = s0.core.mem z := by
      intro z z1 z2; rw [k9, hagM1 z z1 z2]
    -- 3. the test node
    obtain ⟨t3, ht3, n1, n2, n3, n4, n5, n6, n7, n8, n9, n10, n11, n12, n13, n14, n15, n16, n17, n18,
        n19, n20, n21, n22⟩ :=
      node_part Q off hE A s0 ilo ihi rlo rhi T b hbN u v sp s2 k1 k2 hC2 k3
        (by rw [fr2 15 (by omega), h15]) (by rw [fr2 16 (by omega), h16]) (by rw [fr2 1 (by omega), h1])
        (by rw [fr2 47 (by omega), h47]) (by omega) hu0 hv0 hA0 hihi hrhi hR2 hagI2 hagM2
    set s3 := run Q s2 detTape t3 with hs3
    have fr3 : ∀ x, (x < 40 ∨ x = 48) → x ≠ 15 → x ≠ 16 → s3.core.ptrs x = s.core.ptrs x := by
      intro x hx x1 x2
      rw [n19 x x1 x2 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega), fr2 x (by omega)]
    have hC3 : Consts s3 A := consts_of hC2 (fun x hx => n19 x (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    have im3 : ∀ z, A - 5 * (size T : ℤ) ≤ z → z < 0 → s3.integerMemory z = s2.integerMemory z := by
      intro z z1 z2; exact n17 z (by omega) (by omega) (by omega) (Or.inr (by omega))
    have hR3 : Recs s0 ilo ihi rlo rhi A T s3 :=
      recs_frame hR2 (fun z z1 z2 _ => im3 z z1 (by omega))
    have hM3 : Marks A T R s3 := marks_of hM1 (fun k hk => by
      rw [im3 _ (by unfold fa; omega) (by unfold fa; omega), k10])
    have hagI3 : ∀ z, ilo ≤ z → z < ihi → s3.integerMemory z = s0.integerMemory z := by
      intro z z1 z2; rw [im3 z (by omega) (by omega), hagI2 z z1 z2]
    have hagM3 : ∀ z, rlo ≤ z → z < rhi → s3.core.mem z = s0.core.mem z := by
      intro z z1 z2; rw [n18 z (by omega), hagM2 z z1 z2]
    -- 4. the yes subtree
    obtain ⟨t4, u1, v1, ht4, y1, y2, y3, y4, y5, y6, y7, y8, y9, y10, y11, y12, y13, y14, y15, y16, y17,
        y18, y19, y20⟩ :=
      IH b R s3 (sp - 4) (u + 4) (v + 2 * m) hbN hbc.2.2 n1 n2 hC3
        (by rw [fr3 1 (by omega) (by omega) (by omega), h1])
        (by rw [fr3 48 (by omega) (by omega) (by omega), h48]) n5 (by omega)
        (by rw [n6, fr2 49 (by omega), h49]; push_cast; ring) n7 n3 n4 (by omega) (by omega)
        hR3 hM3 hagI3 hagM3
    set s4 := run Q s3 detTape t4 with hs4
    have im4 : ∀ z, (z < sp - 4 - 4 * f ∨ sp - 4 ≤ z) → (z < u + 4 ∨ u1 ≤ z) →
        (∀ k < size T, z ≠ fa A 3 k ∧ z ≠ fa A 4 k) → s4.integerMemory z = s3.integerMemory z := y16
    have frame_cell : ∀ z, sp - 4 ≤ z → z < sp → s4.integerMemory z = s3.integerMemory z := by
      intro z z1 z2
      exact im4 z (Or.inr z1) (Or.inl (by omega)) (fun k hk => ⟨by unfold fa; omega, by unfold fa; omega⟩)
    -- 5. return: pop, patch, mark
    obtain ⟨t5, ht5, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13⟩ :=
      ret_part Q off hE A s0 ilo ihi rlo rhi T b hbN j u f sp (A - 5 * (size T : ℤ)) s4 y1 y2 y3 y6
        (by rw [y5, fr3 48 (by omega) (by omega) (by omega), h48]) hsp (by omega) hu0 hA0
        (by rw [frame_cell _ (by omega) (by omega), n11, fr2 50 (by omega), h50])
        (by rw [frame_cell _ (by omega) (by omega), n12])
        (by rw [frame_cell _ (by omega) (by omega), n13])
        (by rw [frame_cell _ (by omega) (by omega), n14, fr2 49 (by omega), h49])
        y14
    set s5 := run Q s4 detTape t5 with hs5
    have hC5 : Consts s5 A := consts_of y3 (fun x hx => r9 x (by omega) (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega))
    have fr5 : ∀ x, (x < 40 ∨ x = 48) → x ≠ 15 → x ≠ 16 → s5.core.ptrs x = s.core.ptrs x := by
      intro x hx x1 x2
      rw [r9 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega)]
      rcases hx with hx | hx
      · rw [y4 x hx x1 x2, fr3 x (Or.inl hx) x1 x2]
      · subst hx; rw [y5, fr3 48 (Or.inr rfl) (by omega) (by omega)]
    have im5 : ∀ z, z ≠ u + 3 → (∀ k : ℕ, b ≤ k → k < b + S T b → z ≠ fa A 3 k) →
        s5.integerMemory z = s4.integerMemory z := r8
    have hR5 : Recs s0 ilo ihi rlo rhi A T s5 :=
      recs_frame y14 (fun z _ z2 hz => im5 z (by omega) (fun k _ k2 => (hz k (by omega)).1))
    set R' := insert (P T b) R with hR'
    have hM5 : Marks A T R' s5 := by
      intro k hk
      by_cases hkb : b ≤ k ∧ k < b + S T b
      · rw [r7 k hkb.1 hkb.2, if_neg (fun h => ((unc_insert T R b k hbN hk).1 h).2 hkb)]
      · rw [im5 _ (by unfold fa; omega) (fun k' k1 k2 => by unfold fa; omega)]
        rw [y15 k hk (by omega), hM3 k hk]
        have := unc_insert T R b k hbN hk
        by_cases hu' : unc T R k
        · rw [if_pos hu', if_pos (this.2 ⟨hu', hkb⟩)]
        · rw [if_neg hu', if_neg (fun h => hu' (this.1 h).1)]
    have hagI5 : ∀ z, ilo ≤ z → z < ihi → s5.integerMemory z = s0.integerMemory z := by
      intro z z1 z2
      rw [im5 z (by omega) (fun k _ _ => by unfold fa; omega),
        im4 z (Or.inr (by omega)) (Or.inl (by omega)) (fun k _ => ⟨by unfold fa; omega, by unfold fa; omega⟩),
        hagI3 z z1 z2]
    have hagM5 : ∀ z, rlo ≤ z → z < rhi → s5.core.mem z = s0.core.mem z := by
      intro z z1 z2; rw [r11, y17 z (Or.inl (by omega)), hagM3 z z1 z2]
    have hu' : unc T R' j := (unc_insert T R b j hbN hj).2 ⟨hu, by omega⟩
    -- 6. the no subtree
    obtain ⟨t6, u2, v2, ht6, z1, z2, z3, z4, z5, z6, z7, z8, z9, z10, z11, z12, z13, z14, z15, z16, z17,
        z18, z19, z20⟩ :=
      IH j R' s5 sp u1 v1 hj hu' r1 r2 hC5 (by rw [fr5 1 (by omega) (by omega) (by omega), h1])
        (by rw [fr5 48 (by omega) (by omega) (by omega), h48]) r5 hsp r4 r3
        (by rw [r9 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega), y7])
        (by rw [r9 16 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
          (by omega) (by omega) (by omega) (by omega), y8]) (by omega) (by omega) hR5 hM5 hagI5 hagM5
    set s6 := run Q s5 detTape t6 with hs6
    -- the counts
    have hsplit := cnt_split T R j b hj hbc.1 hbc.2.1
    have ha1 := cnt_pos T R b hbc.2.2
    have ha2 := cnt_pos T R' j hu'
    set a1 := cntI T R b with ha1def
    set a2 := cntI T R' j with ha2def
    have hX : ((2 * cntI T R j - 1 : ℕ) : ℤ) = 1 + ((2 * a1 - 1 : ℕ) : ℤ) + ((2 * a2 - 1 : ℕ) : ℤ) := by
      omega
    refine ⟨t1 + t2 + t3 + t4 + t5 + t6, u2, v2, ?_, ?_⟩
    · -- the work
      have e : 2 * cntI T R j - 1 = 1 + (2 * a1 - 1) + (2 * a2 - 1) := by omega
      rw [e, add_mul, add_mul, one_mul]
      have hS1 : S T j ≤ size T := by omega
      have hS2 : S T b ≤ size T := by have := bound T b hbN; omega
      have : t1 + t2 + t3 + t5 ≤ W (size T) m := by unfold W; omega
      generalize (2 * a1 - 1) * W (size T) m = X1 at ht4 ⊢
      generalize (2 * a2 - 1) * W (size T) m = X2 at ht6 ⊢
      omega
    have RR : run Q s detTape (t1 + t2 + t3 + t4 + t5 + t6) = s6 := by
      rw [hs6, hs5, hs4, hs3, hs2, hs1]; simp only [← run_add]
    have CW : cellsWritten Q s (t1 + t2 + t3 + t4 + t5 + t6) =
        cellsWritten Q s t1 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 t3 ∪ cellsWritten Q s3 t4 ∪
          cellsWritten Q s4 t5 ∪ cellsWritten Q s5 t6 := by
      rw [hs5, hs4, hs3, hs2, hs1]; simp only [cellsWritten_add, ← run_add]
    rw [RR, CW]
    -- memory facts of the final state
    have i65 : ∀ z, 0 ≤ z → z < u1 → s6.integerMemory z = s5.integerMemory z := by
      intro z h1' h2'
      exact z16 z (Or.inr (by omega)) (Or.inl h2') (fun k _ => ⟨by unfold fa; omega, by unfold fa; omega⟩)
    have i54 : ∀ z, 0 ≤ z → z ≠ u + 3 → s5.integerMemory z = s4.integerMemory z := by
      intro z h1' h2'; exact im5 z h2' (fun k _ _ => by unfold fa; omega)
    have i43 : ∀ z, 0 ≤ z → z < u + 4 → s4.integerMemory z = s3.integerMemory z := by
      intro z h1' h2'
      exact im4 z (Or.inr (by omega)) (Or.inl h2') (fun k _ => ⟨by unfold fa; omega, by unfold fa; omega⟩)
    have hyes : Good s6 (u + 4) (v + 2 * m) u1 v1 (balance T f (P T b) R) := by
      refine good_mono y13 ?_ ?_
      · intro z h1' h2'; rw [i65 z (by omega) h2', i54 z (by omega) (by omega)]
      · intro z h1' h2'; rw [z17 z (Or.inl h2'), r11]
    refine ⟨z1, z2, z3, ?_, by rw [z5, fr5 48 (by omega) (by omega) (by omega)], z6, z7, z8, by omega,
      by rw [hX]; omega, by omega, ?_, ?_, z14, ?_, ?_, ?_, ?_, by rw [z19, r12, y19, n21, k11, g11]; ring,
      ?_⟩
    · intro x x1 x2 x3; rw [z4 x x1 x2 x3, fr5 x (Or.inl x1) x2 x3]
    · rw [hX]
      have e1 : v1 ≤ v + 2 * m + 2 * m * ((2 * a1 - 1 : ℕ) : ℤ) := y12
      have e2 : v2 ≤ v1 + 2 * m * ((2 * a2 - 1 : ℕ) : ℤ) := z12
      linarith
    · -- the output tree
      rw [balance_succ T R f j b hj (fun _ => ⟨k4, k5, k6⟩), if_neg htot]
      refine good_test _ _ _ _ u v u1 v1 u2 v2 hv0 ?_ ?_ ?_ ?_ ?_ ?_ hyes z13 (by omega) z9 (by omega) z11
      · rw [i65 u (by omega) (by omega), i54 u (by omega) (by omega), i43 u (by omega) (by omega), n8]
      · rw [i65 (u + 1) (by omega) (by omega), i54 (u + 1) (by omega) (by omega),
          i43 (u + 1) (by omega) (by omega), n9]
      · rw [i65 (u + 2) (by omega) (by omega), i54 (u + 2) (by omega) (by omega),
          i43 (u + 2) (by omega) (by omega), n10]
      · rw [i65 (u + 3) (by omega) (by omega), r6, y7]
      · intro jj; have := jj.isLt
        rw [z17 _ (Or.inl (by omega)), r11, y17 _ (Or.inl (by omega)), n15 jj]
      · intro jj; have := jj.isLt
        rw [z17 _ (Or.inl (by omega)), r11, y17 _ (Or.inl (by omega)), n16 jj]
    · -- marks outside the subtree of j
      intro k hk hout
      rw [z15 k hk hout, im5 _ (by unfold fa; omega) (fun k' k1' k2' => by unfold fa; omega),
        y15 k hk (by omega), im3 _ (by unfold fa; omega) (by unfold fa; omega), k10,
        im1 _ (Or.inr (Or.inr (fun k' _ => by unfold fa; omega)))]
    · -- the integer frame
      intro z hz1 hz2 hz3
      have hz4 : ∀ k : ℕ, b ≤ k → k < b + S T b → z ≠ fa A 3 k := fun k _ k2 => (hz3 k (by omega)).1
      rw [z16 z (by push_cast at hz1 ⊢; omega) (by omega) hz3, im5 z (by omega) hz4,
        im4 z (by push_cast at hz1 ⊢; omega) (by omega) hz3,
        n17 z (by omega) (by omega) (by omega) (by push_cast at hz1 ⊢; omega), k10,
        im1 z (Or.inr (Or.inr (fun k hk => (hz3 k hk).2)))]
    · intro z hz
      rw [z17 z (by omega), r11, y17 z (by omega), n18 z (by omega), k9, g10]
    · intro x hx
      rw [z18 x hx, r10, y18 x hx, n20 x hx, k8, g9]
    · intro c hc
      rw [k12, Finset.union_empty] at hc
      simp only [Finset.mem_union] at hc
      rcases hc with ((((hc | hc) | hc) | hc) | hc)
      · obtain ⟨k, kk1, kk2, rfl⟩ := g12 c hc
        left; exact ⟨rfl, Or.inl ⟨by unfold fa; omega, by unfold fa; omega⟩⟩
      · rcases n22 c hc with ⟨e1, e2⟩ | ⟨e1, e2, e3⟩
        · left; refine ⟨e1, Or.inr ?_⟩
          rcases e2 with e2 | e2 | e2 | ⟨e2, e3⟩
          · right; omega
          · right; omega
          · right; omega
          · left; push_cast; omega
        · right; exact ⟨e1, e2, by omega⟩
      · rcases y20 c hc with ⟨e1, e2⟩ | ⟨e1, e2, e3⟩
        · left; refine ⟨e1, ?_⟩
          rcases e2 with e2 | ⟨e2, e3⟩ | ⟨e2, e3⟩
          · left; exact e2
          · right; left; push_cast; omega
          · right; right; omega
        · right; exact ⟨e1, by omega, by omega⟩
      · rcases r13 c hc with rfl | ⟨k, kk1, kk2, rfl⟩
        · left; exact ⟨rfl, Or.inr (Or.inr ⟨by omega, by omega⟩)⟩
        · left; exact ⟨rfl, Or.inl ⟨by unfold fa; omega, by unfold fa; omega⟩⟩
      · rcases z20 c hc with ⟨e1, e2⟩ | ⟨e1, e2, e3⟩
        · left; refine ⟨e1, ?_⟩
          rcases e2 with e2 | ⟨e2, e3⟩ | ⟨e2, e3⟩
          · left; exact e2
          · right; left; push_cast; omega
          · right; right; omega
        · right; exact ⟨e1, by omega, e3⟩

/-- **The recursion**, for every fuel. -/
theorem call_all (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (A : ℤ) (s0 : State)
    (ilo ihi rlo rhi : ℤ) (T : BSP m) (hA : A ≤ ilo) (hA0 : A ≤ 0) (hihi : ihi ≤ 0) (hrhi : rhi ≤ 0) :
    ∀ f, CallOK Q off A s0 ilo ihi rlo rhi T f := by
  intro f
  induction f with
  | zero => exact call_zero Q off hE A s0 ilo ihi rlo rhi T hA hA0 hihi
  | succ f ih => exact call_succ Q off hE A s0 ilo ihi rlo rhi T hA hA0 hihi hrhi f ih

end DetANN.HPIM.BB

-- ===== BB_Main =====
namespace DetANN.HPIM.BB

open PNormReg PNormRegLib DetANN DetANN.HPIM DetANN.HPIM.PP DetANN.HPIM.QP

/-- Offset 48: `i := N`. -/
lemma seg_dfsdone (Q : Program) (off : ℕ) (hE : Embeds Q (bb off) off) (s : State)
    (hpc : s.core.pc = off + 48) (hh : s.halted = false) :
    (run Q s detTape 1).core.pc = off + 49 ∧ (run Q s detTape 1).halted = false ∧
      (run Q s detTape 1).core.ptrs 46 = s.core.ptrs 41 ∧
      (∀ x, x ≠ 46 → (run Q s detTape 1).core.ptrs x = s.core.ptrs x) ∧
      (run Q s detTape 1).core.regs = s.core.regs ∧ (run Q s detTape 1).core.mem = s.core.mem ∧
      (run Q s detTape 1).integerMemory = s.integerMemory ∧
      (run Q s detTape 1).work = s.work + 1 ∧ cellsWritten Q s 1 = ∅ :=
  walk_steps.2.2.2.2.2.2.2.2.1 Q off hE s hpc hh

lemma cnt_le_size {m : ℕ} (T : BSP m) (R : Finset (List Bool)) : cntI T R 0 ≤ size T := by
  unfold cntI
  calc ((Finset.Ico 0 (0 + S T 0)).filter (unc T R)).card ≤ (Finset.Ico 0 (0 + S T 0)).card :=
        Finset.card_filter_le _ _
    _ = size T := by rw [Nat.card_Ico, S_zero]; omega

set_option maxHeartbeats 4000000 in
theorem balance_block' :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m : ℕ) (T : BSP m) (s : State) (ilo ihi rlo rhi : ℤ),
        1 ≤ m → s.core.pc = off → s.halted = false → s.core.ptrs 1 = m →
        BSPAt m s ilo ihi rlo rhi (s.core.ptrs 17) T → ihi ≤ 0 → rhi ≤ 0 →
        s.core.ptrs 13 ≤ ilo → s.core.ptrs 14 ≤ rlo → 0 ≤ s.core.ptrs 15 → 0 ≤ s.core.ptrs 16 →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
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
          (run Q s detTape t).work ≤ s.work + C * (T.paths.card + 1) ^ 2 * (m + 1) := by
  refine ⟨bb, 254, 300, bb_block, fun off Q hE m T s ilo ihi rlo rhi hm hpc hh h1 hB hihi hrhi h13 h14
    h15 h16 => ?_⟩
  set A := s.core.ptrs 13 with hAdef
  have hcard : T.paths.card = size T := paths_card T
  have hN1 : 1 ≤ size T := size_pos T
  obtain ⟨b1, b2, -⟩ := bsp_info hB
  have hA0 : A ≤ 0 := by omega
  -- 1. setup
  obtain ⟨g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12⟩ := seg_setup Q off hE s hpc hh
  set s1 := run Q s detTape 15 with hs1
  -- 2. the walk
  obtain ⟨t2, ht2, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12⟩ :=
    visit Q off hE A s ilo ihi rlo rhi h13 T s1 (s.core.ptrs 17) (-1) 0 g1 g2 g3 hB
      (fun z _ _ => by rw [g10]) g5 g4 g6
  set s2 := run Q s1 detTape t2 with hs2
  -- 3. exit and `i := N`
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := seg_exit Q off hE A s2 w1 w2 w3 w5
  set s3 := run Q s2 detTape 1 with hs3
  obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8, d9⟩ := seg_dfsdone Q off hE s3 e1 e2
  set s4 := run Q s3 detTape 1 with hs4
  have ec : s3.core.ptrs = s2.core.ptrs ∧ s3.core.regs = s2.core.regs ∧ s3.core.mem = s2.core.mem := by
    rw [e3]; exact ⟨rfl, rfl, rfl⟩
  have hC4 : Consts s4 A := consts_of w3 (fun x hx => by rw [d4 x (by omega), ec.1])
  -- 4. sizes and marks
  obtain ⟨t5, ht5, q1, q2, q3, q4, q5, q6, q7, q8, q9⟩ :=
    sz_loop Q off hE A T (size T) s4 d1 d2 hC4 (by rw [d3, ec.1, w4]; simp) le_rfl
      (fun k hk => by rw [d7, e4]; have := (w6 k hk).1; rwa [Nat.zero_add] at this)
      (fun k k1 k2 => by omega)
  set s5 := run Q s4 detTape t5 with hs5
  have hC5 : Consts s5 A := consts_of hC4 (fun x hx => q5 x (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega))
  -- 5. the start of the recursion
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13⟩ :=
    seg_start Q off hE A (size T) s5 q1 q2 hC5 (by
      rw [q5 41 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
        d4 41 (by omega), ec.1, w4]; simp)
  set s6 := run Q s5 detTape 9 with hs6
  have hC6 : Consts s6 A := consts_of hC5 (fun x hx => r8 x (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega))
  -- the low registers before the call
  have lowP : ∀ x, x < 40 → x ≠ 17 → s6.core.ptrs x = s.core.ptrs x := by
    intro x hx x17
    rw [r8 x x17 (by omega) (by omega) (by omega) (by omega) (by omega),
      q5 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      d4 x (by omega), ec.1,
      w8 x (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g7 x hx]
  have regs6 : s6.core.regs = s.core.regs := by rw [r9, q6, d5, ec.2.1, w9, g8]
  have mem6 : s6.core.mem = s.core.mem := by rw [r10, q7, d6, ec.2.2, w10, g9]
  have im6 : ∀ z, A ≤ z → s6.integerMemory z = s.integerMemory z := by
    intro z hz
    rw [r11, q4 z (fun k _ => ⟨by unfold fa; omega, by unfold fa; omega⟩), d7, e4,
      w7 z (Or.inr (by simp; omega)), g10]
  have hR6 : Recs s ilo ihi rlo rhi A T s6 := by
    intro k hk
    have hk4 : s6.integerMemory (fa A 0 k) = s2.integerMemory (fa A 0 k) := by
      rw [r11, q4 _ (fun k' _ => ⟨by unfold fa; omega, by unfold fa; omega⟩), d7, e4]
    have hk5 : s6.integerMemory (fa A 1 k) = s2.integerMemory (fa A 1 k) := by
      rw [r11, q4 _ (fun k' _ => ⟨by unfold fa; omega, by unfold fa; omega⟩), d7, e4]
    obtain ⟨x1, x2⟩ := w6 k hk
    rw [Nat.zero_add] at x1 x2
    refine ⟨by rw [hk4, x1], by rw [hk5]; exact x2, by rw [r11]; exact (q3 k hk).1⟩
  have hM6 : Marks A T ∅ s6 := by
    intro k hk
    rw [r11, (q3 k hk).2, if_pos (show unc T ∅ k from fun c hc => by simp at hc)]
  -- 6. the recursion
  obtain ⟨t7, u', v', ht7, c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17,
      c18, c19, c20⟩ :=
    call_all Q off hE A s ilo ihi rlo rhi T h13 hA0 hihi hrhi (size T + 1) 0 ∅ s6 (A - 5 * (size T : ℤ))
      (s.core.ptrs 15) (s.core.ptrs 16) hN1 (fun c hc => by simp at hc) r1 r2 hC6
      (by rw [lowP 1 (by omega) (by omega), h1]) r3 r4 le_rfl r5 r6
      (by rw [lowP 15 (by omega) (by omega)]) (by rw [lowP 16 (by omega) (by omega)]) h15 h16 hR6 hM6
      (fun z z1 z2 => im6 z (by omega)) (fun z _ _ => by rw [mem6])
  set s7 := run Q s6 detTape t7 with hs7
  -- 7. the end
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := seg_end Q off hE s7 c1 c2 (by rw [c5, c6, r3])
  set s8 := run Q s7 detTape 1 with hs8
  have core8 : s8.core.ptrs = s7.core.ptrs ∧ s8.core.regs = s7.core.regs ∧ s8.core.mem = s7.core.mem := by
    rw [f3]; exact ⟨rfl, rfl, rfl⟩
  have ha := cnt_le_size T ∅
  refine ⟨15 + t2 + 1 + 1 + t5 + 9 + t7 + 1, ?_⟩
  have RR : run Q s detTape (15 + t2 + 1 + 1 + t5 + 9 + t7 + 1) = s8 := by
    rw [hs8, hs7, hs6, hs5, hs4, hs3, hs2, hs1]; simp only [← run_add]
  have CW : cellsWritten Q s (15 + t2 + 1 + 1 + t5 + 9 + t7 + 1) =
      cellsWritten Q s 15 ∪ cellsWritten Q s1 t2 ∪ cellsWritten Q s2 1 ∪ cellsWritten Q s3 1 ∪
        cellsWritten Q s4 t5 ∪ cellsWritten Q s5 9 ∪ cellsWritten Q s6 t7 ∪ cellsWritten Q s7 1 := by
    rw [hs7, hs6, hs5, hs4, hs3, hs2, hs1]; simp only [cellsWritten_add, ← run_add]
  rw [RR]
  have p15 : s8.core.ptrs 15 = u' := by rw [core8.1, c7]
  have p16 : s8.core.ptrs 16 = v' := by rw [core8.1, c8]
  have p17 : s8.core.ptrs 17 = s.core.ptrs 15 := by
    rw [core8.1, c4 17 (by omega) (by omega) (by omega), r7, q5 15 (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega) (by omega), d4 15 (by omega), ec.1,
      w8 15 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega),
      g7 15 (by omega)]
  have hX : ((2 * cntI T ∅ 0 - 1 : ℕ) : ℤ) ≤ 2 * (size T : ℤ) := by omega
  refine ⟨f1, f2, ?_, ⟨?_, ?_⟩, by rw [p15]; exact c9, ?_, by rw [p16]; exact c11, ?_, ?_, ?_⟩
  · -- the output tree
    intro s'' hI hM
    rw [p17, hcard, ← P_zero T]
    have hG := good_mono c13 (fun z _ _ => by rw [f4]) (fun z _ _ => by rw [core8.2.2])
    exact hG s'' (fun z z1 z2 => hI z z1 (by rw [p15]; exact z2))
      (fun z z1 z2 => hM z z1 (by rw [p16]; exact z2))
  · intro x hx hx'
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hx'
    rw [core8.1, c4 x hx hx'.1 hx'.2.1, lowP x hx hx'.2.2]
  · intro x hx _
    rw [core8.2.1, c18 x (by omega), regs6]
  · rw [p15, hcard]
    have : u' ≤ s.core.ptrs 15 + 4 * ((2 * cntI T ∅ 0 - 1 : ℕ) : ℤ) := c10
    push_cast; omega
  · rw [p16, hcard]
    have e : v' ≤ s.core.ptrs 16 + 2 * m * ((2 * cntI T ∅ 0 - 1 : ℕ) : ℤ) := c12
    have hm0 : (0 : ℤ) ≤ m := by positivity
    have h1' : 2 * (m : ℤ) * ((2 * cntI T ∅ 0 - 1 : ℕ) : ℤ) ≤ 2 * m * (2 * (size T : ℤ)) :=
      mul_le_mul_of_nonneg_left hX (by positivity)
    have hmN : (0 : ℤ) ≤ m * size T := by positivity
    push_cast
    linarith
  · -- the writes
    intro c hc
    rw [CW] at hc
    rw [g12, e6, d9, r13, f6] at hc
    simp only [Finset.union_empty, Finset.empty_union] at hc
    simp only [Finset.mem_union] at hc
    rw [hcard]
    have hfr : ∀ z, A - 5 * (size T : ℤ) - 4 * ((size T + 1 : ℕ) : ℤ) ≤ z → z < A →
        A - (300 : ℕ) * ((size T : ℤ) + 1) ≤ z ∧ z < A := by
      intro z z1 z2; push_cast at z1 ⊢; constructor <;> omega
    rcases hc with (hc | hc) | hc
    · obtain ⟨k1, k2, k3⟩ := w12 c hc
      left; rw [k1]; simp only [Bool.false_eq_true, if_false]
      exact hfr _ (by push_cast at k2 ⊢; omega) (by push_cast at k3 ⊢; omega)
    · obtain ⟨k1, k2, k3⟩ := q9 c hc
      left; rw [k1]; simp only [Bool.false_eq_true, if_false]
      exact hfr _ (by omega) k3
    · rcases c20 c hc with ⟨k1, k2⟩ | ⟨k1, k2, k3⟩
      · rw [k1]; simp only [Bool.false_eq_true, if_false]
        rcases k2 with ⟨k2, k3⟩ | ⟨k2, k3⟩ | ⟨k2, k3⟩
        · left; exact hfr _ (by omega) k3
        · left; exact hfr _ (by push_cast at k2 ⊢; omega) (by omega)
        · right; exact ⟨k2, by rw [core8.1, c7]; exact k3⟩
      · right; rw [k1]; simp only [if_true]; exact ⟨k2, by rw [core8.1, c8]; exact k3⟩
  · -- the work
    rw [f5, c19, r12, q8, d8, e5, w11, g11, hcard]
    have hW : (2 * cntI T ∅ 0 - 1) * W (size T) m ≤ 120 * (size T * size T) + 28 * (size T * m) +
        180 * size T := by
      calc (2 * cntI T ∅ 0 - 1) * W (size T) m ≤ (2 * size T) * W (size T) m :=
            Nat.mul_le_mul_right _ (by omega)
        _ = 120 * (size T * size T) + 28 * (size T * m) + 180 * size T := by unfold W; ring
    have e : 300 * (size T + 1) ^ 2 * (m + 1) = 300 * (size T * size T * m) + 300 * (size T * size T) +
        600 * (size T * m) + 600 * size T + 300 * m + 300 := by ring
    rw [e]
    have : size T * size T ≤ size T * size T * m + size T * size T := by omega
    generalize size T * size T * m = P3 at this ⊢
    generalize size T * size T = P2 at hW this ⊢
    generalize size T * m = Pm at hW ⊢
    omega

end DetANN.HPIM.BB

namespace DetANN.HPIM

open PNormReg PNormRegLib

theorem _root_.solution :
    ∃ blk : ℕ → Program, ∃ L C : ℕ, IsBlock blk L ∧
      ∀ (off : ℕ) (Q : Program), Embeds Q (blk off) off →
      ∀ (m : ℕ) (T : BSP m) (s : State) (ilo ihi rlo rhi : ℤ),
        1 ≤ m → s.core.pc = off → s.halted = false → s.core.ptrs 1 = m →
        BSPAt m s ilo ihi rlo rhi (s.core.ptrs 17) T → ihi ≤ 0 → rhi ≤ 0 →
        s.core.ptrs 13 ≤ ilo → s.core.ptrs 14 ≤ rlo → 0 ≤ s.core.ptrs 15 → 0 ≤ s.core.ptrs 16 →
        ∃ t, (run Q s detTape t).core.pc = off + L ∧ (run Q s detTape t).halted = false ∧
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
          (run Q s detTape t).work ≤ s.work + C * (T.paths.card + 1) ^ 2 * (m + 1) :=
  DetANN.HPIM.BB.balance_block'

end DetANN.HPIM
