-- Prove2me | solution 1 for CannonFloydParry.isReduced_iff
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-16T22:04:11.799582+00:00
-- url     : https://prove2.me/submissions/5872cdb5-b9b2-40fc-aabe-49d98efcd316

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib

namespace CannonFloydParry

/-! ### Lengths -/

lemma one_le_leafCount (t : TTree) : 1 ≤ t.leafCount := by
  induction t with
  | leaf => simp [TTree.leafCount]
  | node l r ihl ihr => rw [TTree.leafCount]; omega

lemma incrHead_length (l : List ℕ) : (TTree.incrHead l).length = l.length := by
  cases l with
  | nil => rfl
  | cons a as => rfl

lemma leftRuns_length (t : TTree) : t.leftRuns.length = t.leafCount := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      rw [TTree.leftRuns, TTree.leafCount, List.length_append, incrHead_length, ihl, ihr]

lemma exponents_length (t : TTree) : t.exponents.length = t.leafCount := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      rw [TTree.exponents, TTree.leafCount, List.length_append, leftRuns_length, ihr]

/-! ### Unfolding `caretAt` and `endsInCaret`

Both are defined by overlapping pattern matches, so they are unfolded here through `rfl`
equations rather than by rewriting with the definitions. -/

lemma caretAt_leaf (k : ℕ) : TTree.leaf.caretAt k = false := rfl

lemma caretAt_node (l r : TTree) (k : ℕ) :
    (TTree.node l r).caretAt k =
      if k + 1 < l.leafCount then l.caretAt k
      else if l.leafCount ≤ k then r.caretAt (k - l.leafCount)
      else (match l, r with
            | TTree.leaf, TTree.leaf => true
            | _, _ => false) := rfl

lemma caretAt_node_left {l r : TTree} {k : ℕ} (h : k + 1 < l.leafCount) :
    (TTree.node l r).caretAt k = l.caretAt k := by
  rw [caretAt_node, if_pos h]

lemma caretAt_node_right {l r : TTree} {k : ℕ} (h1 : ¬ (k + 1 < l.leafCount))
    (h2 : l.leafCount ≤ k) :
    (TTree.node l r).caretAt k = r.caretAt (k - l.leafCount) := by
  rw [caretAt_node, if_neg h1, if_pos h2]

lemma caretAt_node_straddle_false {l r : TTree} {k : ℕ} (h1 : ¬ (k + 1 < l.leafCount))
    (h2 : ¬ (l.leafCount ≤ k)) (h3 : l ≠ TTree.leaf ∨ r ≠ TTree.leaf) :
    (TTree.node l r).caretAt k = false := by
  rw [caretAt_node, if_neg h1, if_neg h2]
  cases l with
  | leaf =>
      cases r with
      | leaf => rcases h3 with h3 | h3 <;> exact absurd rfl h3
      | node c e => rfl
  | node a b =>
      cases r with
      | leaf => rfl
      | node c e => rfl

lemma caretAt_leaf_leaf_zero : (TTree.node TTree.leaf TTree.leaf).caretAt 0 = true := rfl

lemma endsInCaret_leaf : TTree.leaf.endsInCaret = false := rfl

lemma endsInCaret_leaf_leaf : (TTree.node TTree.leaf TTree.leaf).endsInCaret = true := rfl

lemma endsInCaret_right_leaf {l : TTree} (h : l ≠ TTree.leaf) :
    (TTree.node l TTree.leaf).endsInCaret = false := by
  cases l with
  | leaf => exact absurd rfl h
  | node a b => rfl

lemma endsInCaret_node_node (l a b : TTree) :
    (TTree.node l (TTree.node a b)).endsInCaret = (TTree.node a b).endsInCaret := by
  cases l with
  | leaf => rfl
  | node c e => rfl

/-! ### `incrHead` touches only the head -/

lemma incrHead_getD_zero {l : List ℕ} (h : l ≠ []) :
    (TTree.incrHead l).getD 0 0 = l.getD 0 0 + 1 := by
  cases l with
  | nil => exact absurd rfl h
  | cons a as => rfl

lemma incrHead_getD_succ (l : List ℕ) (k : ℕ) :
    (TTree.incrHead l).getD (k + 1) 0 = l.getD (k + 1) 0 := by
  cases l with
  | nil => rfl
  | cons a as => rfl

/-! ### The first and last left-runs

The leftmost leaf of a node is a left child, so its run is positive; the rightmost leaf of any
tree is a right child (or the whole tree), so its run is zero. -/

lemma leftRuns_ne_nil (t : TTree) : t.leftRuns ≠ [] := by
  intro h
  have hlen := leftRuns_length t
  have := one_le_leafCount t
  rw [h] at hlen
  simp at hlen
  omega

lemma leftRuns_getD_zero_node (l r : TTree) : 0 < (TTree.node l r).leftRuns.getD 0 0 := by
  have hne : l.leftRuns ≠ [] := leftRuns_ne_nil l
  rw [TTree.leftRuns,
    List.getD_append _ _ _ _ (by rw [incrHead_length]; exact List.length_pos_iff.mpr hne),
    incrHead_getD_zero hne]
  omega

lemma leftRuns_getD_last (t : TTree) : t.leftRuns.getD (t.leafCount - 1) 0 = 0 := by
  induction t with
  | leaf => rfl
  | node l r ihl ihr =>
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      have hlenL : (TTree.incrHead l.leftRuns).length = l.leafCount := by
        rw [incrHead_length, leftRuns_length]
      have hidx : (TTree.node l r).leafCount - 1 = l.leafCount + (r.leafCount - 1) := by
        rw [TTree.leafCount]; omega
      rw [TTree.leftRuns, hidx,
        List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL]
      simpa using ihr

/-! ### Carets and left-runs

The `k`th and `(k+1)`th leaves are siblings exactly when the left-run from the `k`th is positive
and the run from the `(k+1)`th is zero: the first says the `k`th leaf is a left child, the second
that the `(k+1)`th is a right child, and adjacency then forces them to share a parent. -/

lemma caretAt_iff_leftRuns : ∀ (t : TTree) (k : ℕ),
    (t.caretAt k = true ↔ (0 < t.leftRuns.getD k 0 ∧ t.leftRuns.getD (k + 1) 0 = 0)) := by
  intro t
  induction t with
  | leaf =>
      intro k
      have h1 : (TTree.leaf.leftRuns).getD k 0 = 0 := by
        show ([0] : List ℕ).getD k 0 = 0
        cases k with
        | zero => rfl
        | succ k => rfl
      rw [caretAt_leaf, h1]
      constructor
      · intro h; exact Bool.noConfusion h
      · intro h; exact absurd h.1 (lt_irrefl 0)
  | node l r ihl ihr =>
      intro k
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      have hlenL : (TTree.incrHead l.leftRuns).length = l.leafCount := by
        rw [incrHead_length, leftRuns_length]
      rw [TTree.leftRuns]
      rcases Nat.lt_or_ge (k + 1) l.leafCount with hk1 | hk1
      · -- the pair lies inside the left subtree
        rw [caretAt_node_left hk1,
          List.getD_append _ _ _ _ (by rw [hlenL]; omega),
          List.getD_append _ _ _ _ (by rw [hlenL]; omega)]
        cases k with
        | zero =>
            -- the head is the one entry `incrHead` changes, but it was positive anyway
            obtain ⟨a, b, rfl⟩ : ∃ a b, l = TTree.node a b := by
              cases l with
              | leaf => exfalso; rw [TTree.leafCount] at hk1; omega
              | node a b => exact ⟨a, b, rfl⟩
            have hpos : 0 < (TTree.node a b).leftRuns.getD 0 0 := leftRuns_getD_zero_node a b
            rw [incrHead_getD_zero (leftRuns_ne_nil (TTree.node a b)), incrHead_getD_succ,
              ihl 0]
            constructor
            · exact fun h => ⟨by omega, h.2⟩
            · exact fun h => ⟨hpos, h.2⟩
        | succ j =>
            rw [incrHead_getD_succ, incrHead_getD_succ]
            exact ihl (j + 1)
      · rcases Nat.lt_or_ge k l.leafCount with hk2 | hk2
        · -- the pair straddles the two subtrees: `k + 1 = l.leafCount`
          rw [List.getD_append _ _ _ _ (by rw [hlenL]; omega),
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL]
          cases l with
          | leaf =>
              -- `l` is a single leaf, so its (incremented) entry is `1`
              have hk0 : k = 0 := by
                rw [TTree.leafCount] at hk2; omega
              subst hk0
              have hone : (TTree.incrHead (TTree.leaf.leftRuns)).getD 0 0 = 1 := rfl
              rw [hone, show (0 : ℕ) + 1 - TTree.leaf.leafCount = 0 from rfl]
              cases r with
              | leaf =>
                  rw [caretAt_leaf_leaf_zero]
                  have : (TTree.leaf.leftRuns).getD 0 0 = 0 := rfl
                  rw [this]
                  simp
              | node c e =>
                  have hpos : 0 < (TTree.node c e).leftRuns.getD 0 0 :=
                    leftRuns_getD_zero_node c e
                  rw [caretAt_node_straddle_false (by rw [TTree.leafCount]; omega)
                    (by rw [TTree.leafCount]; omega) (Or.inr (by intro h; exact TTree.noConfusion h))]
                  constructor
                  · intro h; exact Bool.noConfusion h
                  · intro h; exact absurd h.2 (by omega)
          | node a b =>
              -- the left entry is the last left-run of `l`, which is `0`
              have hna := one_le_leafCount a
              have hnb := one_le_leafCount b
              have hk1' : 1 ≤ k := by rw [TTree.leafCount] at hk1 hk2; omega
              obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
              rw [incrHead_getD_succ]
              have hzero : (TTree.node a b).leftRuns.getD (j + 1) 0 = 0 := by
                have h := leftRuns_getD_last (TTree.node a b)
                rw [show (TTree.node a b).leafCount - 1 = j + 1 by
                  rw [TTree.leafCount] at hk1 hk2 ⊢; omega] at h
                exact h
              rw [hzero, caretAt_node_straddle_false (by omega) (by omega)
                (Or.inl (by intro h; exact TTree.noConfusion h))]
              constructor
              · intro h; exact Bool.noConfusion h
              · intro h; exact absurd h.1 (lt_irrefl 0)
        · -- the pair lies inside the right subtree
          rw [caretAt_node_right (by omega) hk2,
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega),
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL,
            show k + 1 - l.leafCount = (k - l.leafCount) + 1 by omega]
          exact ihr (k - l.leafCount)

/-- Past the last adjacent pair there is no caret. -/
lemma caretAt_of_le : ∀ (t : TTree) (k : ℕ), t.leafCount ≤ k + 1 → t.caretAt k = false := by
  intro t
  induction t with
  | leaf => intro k _; rfl
  | node l r ihl ihr =>
      intro k hk
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      rw [TTree.leafCount] at hk
      rw [caretAt_node_right (by omega) (by omega)]
      exact ihr (k - l.leafCount) (by omega)

/-! ### The exponent at the last pair, and carets read off the exponents -/

lemma exponents_getD_last_pair : ∀ (t : TTree), 2 ≤ t.leafCount →
    t.exponents.getD (t.leafCount - 2) 0 = 0 := by
  intro t
  induction t with
  | leaf => intro h; rw [TTree.leafCount] at h; omega
  | node l r ihl ihr =>
      intro _
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      have hlenL : (l.leftRuns).length = l.leafCount := leftRuns_length l
      rw [TTree.exponents]
      rcases Nat.lt_or_ge r.leafCount 2 with hp2 | hp2
      · -- `r` is a single leaf: the index falls at the last entry of the left block
        rw [show (TTree.node l r).leafCount - 2 = l.leafCount - 1 by rw [TTree.leafCount]; omega,
          List.getD_append _ _ _ _ (by rw [hlenL]; omega)]
        exact leftRuns_getD_last l
      · -- `r` has at least two leaves: recurse into it
        rw [show (TTree.node l r).leafCount - 2 = l.leafCount + (r.leafCount - 2) by
            rw [TTree.leafCount]; omega,
          List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL]
        simpa using ihr hp2

lemma caretAt_iff_exponents : ∀ (t : TTree) (k : ℕ), k + 2 < t.leafCount →
    (t.caretAt k = true ↔ (0 < t.exponents.getD k 0 ∧ t.exponents.getD (k + 1) 0 = 0)) := by
  intro t
  induction t with
  | leaf => intro k hk; rw [TTree.leafCount] at hk; omega
  | node l r ihl ihr =>
      intro k hk
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      rw [TTree.leafCount] at hk
      have hlenL : (l.leftRuns).length = l.leafCount := leftRuns_length l
      rw [TTree.exponents]
      rcases Nat.lt_or_ge (k + 1) l.leafCount with hk1 | hk1
      · -- inside the left subtree, where the exponents restrict to the *left-runs* of `l`
        rw [caretAt_node_left hk1,
          List.getD_append _ _ _ _ (by rw [hlenL]; omega),
          List.getD_append _ _ _ _ (by rw [hlenL]; omega)]
        exact caretAt_iff_leftRuns l k
      · rcases Nat.lt_or_ge k l.leafCount with hk2 | hk2
        · -- straddling: the left entry is the last left-run of `l`, which is `0`
          rw [List.getD_append _ _ _ _ (by rw [hlenL]; omega)]
          have hzero : l.leftRuns.getD k 0 = 0 := by
            rw [show k = l.leafCount - 1 by omega]; exact leftRuns_getD_last l
          have hrne : r ≠ TTree.leaf := by
            intro h
            rw [h, TTree.leafCount] at hk
            omega
          rw [hzero, caretAt_node_straddle_false (by omega) (by omega) (Or.inr hrne)]
          constructor
          · intro h; exact Bool.noConfusion h
          · intro h; exact absurd h.1 (lt_irrefl 0)
        · -- inside the right subtree
          rw [caretAt_node_right (by omega) hk2,
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega),
            List.getD_append_right _ _ _ _ (by rw [hlenL]; omega), hlenL,
            show k + 1 - l.leafCount = (k - l.leafCount) + 1 by omega]
          exact ihr (k - l.leafCount) (by omega)

/-! ### `endsInCaret` is the caret at the last pair -/

lemma endsInCaret_eq_caretAt : ∀ (t : TTree), 2 ≤ t.leafCount →
    t.endsInCaret = t.caretAt (t.leafCount - 2) := by
  intro t
  induction t with
  | leaf => intro h; rw [TTree.leafCount] at h; omega
  | node l r ihl ihr =>
      intro _
      have hm := one_le_leafCount l
      have hp := one_le_leafCount r
      rcases Nat.lt_or_ge r.leafCount 2 with hp2 | hp2
      · -- `r` is a single leaf, so the last pair straddles
        obtain rfl : r = TTree.leaf := by
          cases r with
          | leaf => rfl
          | node a b =>
              exfalso
              have := one_le_leafCount a
              have := one_le_leafCount b
              rw [TTree.leafCount] at hp2
              omega
        rw [show (TTree.node l TTree.leaf).leafCount - 2 = l.leafCount - 1 by
          rw [TTree.leafCount]; omega]
        cases l with
        | leaf => rw [endsInCaret_leaf_leaf]; exact caretAt_leaf_leaf_zero.symm
        | node a b =>
            have hne : TTree.node a b ≠ TTree.leaf := by
              intro h; exact TTree.noConfusion h
            rw [endsInCaret_right_leaf hne,
              caretAt_node_straddle_false (by omega) (by omega) (Or.inl hne)]
      · -- `r` has at least two leaves, so the last pair lies inside it
        obtain ⟨a, b, rfl⟩ : ∃ a b, r = TTree.node a b := by
          cases r with
          | leaf => exfalso; rw [TTree.leafCount] at hp2; omega
          | node a b => exact ⟨a, b, rfl⟩
        rw [endsInCaret_node_node,
          show (TTree.node l (TTree.node a b)).leafCount - 2
              = l.leafCount + ((TTree.node a b).leafCount - 2) by rw [TTree.leafCount]; omega,
          caretAt_node_right (by omega) (by omega),
          show l.leafCount + ((TTree.node a b).leafCount - 2) - l.leafCount
              = (TTree.node a b).leafCount - 2 by omega]
        exact ihr hp2

end CannonFloydParry

open CannonFloydParry

theorem solution (d : TreeDiagram) :
    IsReduced d ↔
      (d.dom.endsInCaret = true → d.ran.endsInCaret = false) ∧
        ∀ k, k + 1 < d.dom.leafCount →
          0 < d.dom.exponents.getD k 0 → 0 < d.ran.exponents.getD k 0 →
            0 < d.dom.exponents.getD (k + 1) 0 ∨ 0 < d.ran.exponents.getD (k + 1) 0 := by
  have hran : d.ran.leafCount = d.dom.leafCount := d.leaves_eq.symm
  constructor
  · intro hred
    refine ⟨?_, ?_⟩
    · -- the last pair
      intro hdom
      rcases Nat.lt_or_ge d.dom.leafCount 2 with h1 | h1
      · -- a one-leaf domain tree ends in no caret, so there is nothing to prove
        exfalso
        have hleaf : d.dom = TTree.leaf := by
          cases hd : d.dom with
          | leaf => rfl
          | node a b =>
              exfalso
              have := one_le_leafCount a
              have := one_le_leafCount b
              rw [hd, TTree.leafCount] at h1
              omega
        rw [hleaf, endsInCaret_leaf] at hdom
        exact Bool.noConfusion hdom
      · by_contra hcon
        simp only [Bool.not_eq_false] at hcon
        rw [endsInCaret_eq_caretAt _ h1] at hdom
        rw [endsInCaret_eq_caretAt _ (by omega : 2 ≤ d.ran.leafCount), hran] at hcon
        exact hred _ ⟨hdom, hcon⟩
    · -- an interior pair
      intro k hk hda hrb
      by_contra hcon
      simp only [not_or, Nat.not_lt, Nat.le_zero] at hcon
      rcases Nat.lt_or_ge (k + 2) d.dom.leafCount with h2 | h2
      · exact hred k ⟨(caretAt_iff_exponents d.dom k h2).mpr ⟨hda, hcon.1⟩,
          (caretAt_iff_exponents d.ran k (by omega)).mpr ⟨hrb, hcon.2⟩⟩
      · -- `k` is the last pair, where the exponent is `0`, so the hypothesis cannot hold
        exfalso
        have h0 := exponents_getD_last_pair d.dom (by omega)
        rw [show d.dom.leafCount - 2 = k by omega] at h0
        omega
  · intro hRHS k hk
    obtain ⟨hA, hB⟩ := hRHS
    obtain ⟨hdc, hrc⟩ := hk
    -- a caret needs the pair to exist
    have hk2 : k + 2 ≤ d.dom.leafCount := by
      by_contra hcon
      rw [caretAt_of_le d.dom k (by omega)] at hdc
      exact Bool.noConfusion hdc
    rcases Nat.lt_or_ge (k + 2) d.dom.leafCount with h2 | h2
    · obtain ⟨hda, hda'⟩ := (caretAt_iff_exponents d.dom k h2).mp hdc
      obtain ⟨hrb, hrb'⟩ := (caretAt_iff_exponents d.ran k (by omega)).mp hrc
      rcases hB k (by omega) hda hrb with h | h
      · rw [hda'] at h; omega
      · rw [hrb'] at h; omega
    · have hkeq : k = d.dom.leafCount - 2 := by omega
      have h1 : 2 ≤ d.dom.leafCount := by omega
      have hdE : d.dom.endsInCaret = true := by
        rw [endsInCaret_eq_caretAt _ h1, ← hkeq]; exact hdc
      have hrE : d.ran.endsInCaret = true := by
        rw [endsInCaret_eq_caretAt _ (by omega : 2 ≤ d.ran.leafCount), hran, ← hkeq]
        exact hrc
      rw [hA hdE] at hrE
      exact Bool.noConfusion hrE
