-- Prove2me | solution 2 for CannonFloydParry.exists_isNormalFormData
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-24T17:59:05.824597+00:00
-- url     : https://prove2.me/submissions/50dd5ea3-2d64-4789-8967-170f9f134afa

import Definitions.Def_CannonFloydParry
import Definitions.Def_CannonFloydParry_Trees
import Definitions.Def_CannonFloydParry_TreeDiagrams
import Mathlib
import Theorems.Thm_CannonFloydParry_represents_word_exponents
import Theorems.Thm_CannonFloydParry_getLast_exponents_eq_zero

namespace CannonFloydParry

/-! ### `extend` of the two generators is the underlying function on the line -/

/-! ### Marks lie strictly inside, and `marksAux` is natural for affine maps -/

/-! ### `A` is the rotation at the root

`A` carries `[0,1/2]`, `[1/2,3/4]`, `[3/4,1]` affinely onto `[0,1/4]`, `[1/4,1/2]`, `[1/2,1]`.
Reading those as the three blocks of `node l (node x y)` and of `node (node l x) y`, `A` carries
the marks of the first tree to the marks of the second, whatever `l`, `x`, `y` are. -/

/-! ### `B` is the rotation one step down the right side -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### Chains from a uniform relation -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The marks of a tree increase -/

lemma one_le_leafCount' (t : TTree) : 1 ≤ t.leafCount := by
  induction t with
  | leaf => simp [TTree.leafCount]
  | node l r ihl ihr => rw [TTree.leafCount]; omega

/-! ### Every point of `[0,1]` lies in one of the pieces -/

/-! ### An element is determined by its diagram -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The two generators lie in `F` -/

/-! ### Affineness on the pieces, for the two rotations -/

/-! ### The two rotations, as tree diagrams -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### The identity and inverses, as tree diagrams -/

/-! ### Spines: a sequence of left subtrees hanging off the right side -/

/-! ### Words -/

lemma wordFrom_append : ∀ (as bs : List ℕ) (i : ℕ),
    wordFrom i (as ++ bs) = wordFrom i as * wordFrom (i + as.length) bs := by
  intro as
  induction as with
  | nil => intro bs i; rw [List.nil_append, wordFrom]; simp
  | cons a as ih =>
      intro bs i
      have hidx : i + 1 + as.length = i + (a :: as).length := by
        simp only [List.length_cons]; omega
      rw [List.cons_append, wordFrom, wordFrom, ih bs (i + 1), mul_assoc, hidx]

end CannonFloydParry

namespace CannonFloydParry

/-! ### Composition of tree diagrams (the source's rule on p. 222) -/


/-! ### `Xₘ` is the rotation `m` steps down the right side

`X₀ = A` rotates at the root and `X₁ = B` one step down; the recursion
`X_{m+2} = A⁻¹ X_{m+1} A` then pushes the rotation one step further each time, because `A` itself
turns a spine `w₀, w₁, …` into the spine `⟨w₀,w₁⟩, …`, one shorter. -/

end CannonFloydParry

namespace CannonFloydParry

/-! ### Exponents of a spine, and of a rotation -/

/-! ### Trees with all exponents zero are the right combs -/

/-! ### A tree with a positive exponent is a spine over a rotatable node -/

/-! ### Words with total exponent zero are trivial -/

lemma wordFrom_of_sum_eq_zero : ∀ (cs : List ℕ), cs.sum = 0 → ∀ i, wordFrom i cs = 1 := by
  intro cs
  induction cs with
  | nil => intro _ i; rfl
  | cons c cs ih =>
      intro hsum i
      rw [List.sum_cons] at hsum
      have hc : c = 0 := by omega
      have hcs : cs.sum = 0 := by omega
      rw [wordFrom, hc, pow_zero, one_mul, ih hcs (i + 1)]

/-! ### The identity, on a diagram whose two trees happen to coincide -/

/-! ### The induction of the source's proof: peel one rotation at a time -/


end CannonFloydParry

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

end CannonFloydParry

namespace CannonFloydParry

/-! ### `getD` bookkeeping for `ℕ`-lists -/

lemma word_eq (cs : List ℕ) : word cs = wordFrom 0 cs := rfl

lemma getD_ge_length {l : List ℕ} {j : ℕ} (h : l.length ≤ j) : l.getD j 0 = 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

lemma sum_eq_zero_of_getD : ∀ {l : List ℕ}, (∀ k, k < l.length → l.getD k 0 = 0) →
    l.sum = 0 := by
  intro l
  induction l with
  | nil => intro _; rfl
  | cons a as ih =>
      intro h
      have ha : a = 0 := by
        have := h 0 (by simp)
        simpa using this
      have has : as.sum = 0 := by
        refine ih ?_
        intro k hk
        have := h (k + 1) (by simpa using hk)
        simpa using this
      rw [List.sum_cons, ha, has]

lemma getD_drop : ∀ (L : ℕ) (l : List ℕ) (k : ℕ), (l.drop L).getD k 0 = l.getD (L + k) 0 := by
  intro L
  induction L with
  | zero => intro l k; simp
  | succ L ih =>
      intro l k
      cases l with
      | nil => simp
      | cons a as =>
          rw [List.drop_succ_cons, ih as k,
            show L + 1 + k = (L + k) + 1 by omega, List.getD_cons_succ]

lemma getD_take : ∀ (L : ℕ) (l : List ℕ) (k : ℕ), k < L → (l.take L).getD k 0 = l.getD k 0 := by
  intro L
  induction L with
  | zero => intro l k hk; omega
  | succ L ih =>
      intro l k hk
      cases l with
      | nil => simp
      | cons a as =>
          cases k with
          | zero => rw [List.take_succ_cons]; rfl
          | succ j =>
              rw [List.take_succ_cons, List.getD_cons_succ, List.getD_cons_succ]
              exact ih as j (by omega)

/-- Trailing zeros do not change the word. -/
lemma word_take {l : List ℕ} {L : ℕ} (hz : ∀ k, L ≤ k → l.getD k 0 = 0) :
    word (l.take L) = word l := by
  have hdz : (l.drop L).sum = 0 := by
    refine sum_eq_zero_of_getD ?_
    intro k _
    rw [getD_drop]
    exact hz (L + k) (by omega)
  calc word (l.take L)
      = wordFrom 0 (l.take L) * wordFrom (0 + (l.take L).length) (l.drop L) := by
        rw [wordFrom_of_sum_eq_zero _ hdz, mul_one, word_eq]
    _ = wordFrom 0 (l.take L ++ l.drop L) := (wordFrom_append _ _ 0).symm
    _ = word l := by rw [List.take_append_drop, word_eq]

/-! ### The last two exponents of a tree are zero -/

lemma getD_getLastN : ∀ (xs : List ℕ) (v : ℕ), xs.getLast? = some v →
    xs.getD (xs.length - 1) 0 = v := by
  intro xs
  induction xs with
  | nil => intro v h; simp at h
  | cons x rest ih =>
      intro v h
      cases rest with
      | nil =>
          have hxv : x = v := by simpa using h
          simp [hxv]
      | cons y t =>
          have h' : (y :: t).getLast? = some v := by
            rw [List.getLast?_cons_cons] at h; exact h
          have hrec := ih v h'
          show (x :: y :: t).getD (t.length + 1) 0 = v
          rw [List.getD_cons_succ]
          simpa using hrec


lemma exponents_getD_last (t : TTree) : t.exponents.getD (t.leafCount - 1) 0 = 0 := by
  have h := getD_getLastN _ 0 (getLast_exponents_eq_zero t)
  rwa [exponents_length] at h

end CannonFloydParry

open CannonFloydParry

theorem solution {d : TreeDiagram} {f : UI ≃o UI}
    (hd : IsReduced d) (hr : Represents d f) (hne : f ≠ 1) :
    ∃ as bs : List ℕ, IsNormalFormData as bs ∧ f = word bs * (word as)⁻¹ := by
  classical
  have hfeq : f = word d.ran.exponents * (word d.dom.exponents)⁻¹ :=
    represents_word_exponents hr
  have hlenA : d.dom.exponents.length = d.dom.leafCount := exponents_length d.dom
  have hlenB : d.ran.exponents.length = d.dom.leafCount := by
    rw [exponents_length, ← d.leaves_eq]
  -- reducedness, read on the exponents (this is Theorem 2.5's second statement, forward half)
  have hred : ∀ k, k + 2 < d.dom.leafCount →
      0 < d.dom.exponents.getD k 0 → 0 < d.ran.exponents.getD k 0 →
      0 < d.dom.exponents.getD (k + 1) 0 ∨ 0 < d.ran.exponents.getD (k + 1) 0 := by
    intro k hk ha hb
    by_contra hcon
    simp only [not_or, Nat.not_lt, Nat.le_zero] at hcon
    exact hd k ⟨(caretAt_iff_exponents d.dom k hk).mpr ⟨ha, hcon.1⟩,
      (caretAt_iff_exponents d.ran k (by rw [← d.leaves_eq]; exact hk)).mpr ⟨hb, hcon.2⟩⟩
  -- the last two exponents of each tree vanish
  have hA1 : d.dom.exponents.getD (d.dom.leafCount - 1) 0 = 0 := exponents_getD_last d.dom
  have hB1 : d.ran.exponents.getD (d.dom.leafCount - 1) 0 = 0 := by
    rw [d.leaves_eq]; exact exponents_getD_last d.ran
  have hone := one_le_leafCount' d.dom
  have hA2 : ∀ h : 2 ≤ d.dom.leafCount, d.dom.exponents.getD (d.dom.leafCount - 2) 0 = 0 :=
    fun h => exponents_getD_last_pair d.dom h
  have hB2 : ∀ h : 2 ≤ d.dom.leafCount, d.ran.exponents.getD (d.dom.leafCount - 2) 0 = 0 :=
    fun h => by rw [d.leaves_eq]; exact exponents_getD_last_pair d.ran (by rwa [← d.leaves_eq])
  set P : ℕ → Prop := fun j =>
    0 < d.dom.exponents.getD j 0 ∨ 0 < d.ran.exponents.getD j 0 with hP
  -- past the end both lists read as zero
  have hPbig : ∀ j, d.dom.leafCount ≤ j → ¬ P j := by
    intro j hj
    simp only [hP, not_or, Nat.not_lt, Nat.le_zero]
    exact ⟨getD_ge_length (by omega), getD_ge_length (by omega)⟩
  by_cases hex : ∃ j, P j
  · obtain ⟨j₀, hj₀⟩ := hex
    have hj₀lt : j₀ ≤ d.dom.leafCount := by
      by_contra hc
      have hge : d.dom.leafCount ≤ j₀ := by omega
      exact hPbig j₀ hge hj₀
    -- the largest index at which either list is nonzero
    have hspec : P (Nat.findGreatest P d.dom.leafCount) :=
      Nat.findGreatest_spec hj₀lt hj₀
    have hle : Nat.findGreatest P d.dom.leafCount ≤ d.dom.leafCount :=
      Nat.findGreatest_le _
    have hgreat : ∀ k, Nat.findGreatest P d.dom.leafCount < k → ¬ P k := by
      intro k hk
      rcases Nat.lt_or_ge d.dom.leafCount k with h | h
      · exact hPbig k (by omega)
      · exact Nat.findGreatest_is_greatest hk h
    -- it is at least three places from the end
    have hm2 : Nat.findGreatest P d.dom.leafCount + 2 < d.dom.leafCount := by
      have hne1 : Nat.findGreatest P d.dom.leafCount ≠ d.dom.leafCount - 1 := by
        intro hc
        rw [hc] at hspec
        simp only [hP, hA1, hB1] at hspec
        omega
      have hnelen : Nat.findGreatest P d.dom.leafCount ≠ d.dom.leafCount := by
        intro hc
        exact hPbig d.dom.leafCount (le_refl _) (hc ▸ hspec)
      have h2le : 2 ≤ d.dom.leafCount := by omega
      have hne2 : Nat.findGreatest P d.dom.leafCount ≠ d.dom.leafCount - 2 := by
        intro hc
        rw [hc] at hspec
        simp only [hP, hA2 h2le, hB2 h2le] at hspec
        omega
      omega
    set m := Nat.findGreatest P d.dom.leafCount with hmdef
    -- truncate both exponent lists just past `m`
    have hzeroA : ∀ k, m + 1 ≤ k → d.dom.exponents.getD k 0 = 0 := by
      intro k hk
      have := hgreat k (by omega)
      simp only [hP, not_or, Nat.not_lt, Nat.le_zero] at this
      exact this.1
    have hzeroB : ∀ k, m + 1 ≤ k → d.ran.exponents.getD k 0 = 0 := by
      intro k hk
      have := hgreat k (by omega)
      simp only [hP, not_or, Nat.not_lt, Nat.le_zero] at this
      exact this.2
    refine ⟨d.dom.exponents.take (m + 1), d.ran.exponents.take (m + 1), ?_, ?_⟩
    · have hlA : (d.dom.exponents.take (m + 1)).length = m + 1 := by
        rw [List.length_take, hlenA]; omega
      have hlB : (d.ran.exponents.take (m + 1)).length = m + 1 := by
        rw [List.length_take, hlenB]; omega
      refine ⟨by rw [← List.length_pos_iff, hlA]; omega, by rw [hlA, hlB], ?_, ?_⟩
      · -- exactly one of the two last entries is nonzero
        rw [hlA, Nat.add_sub_cancel, getD_take _ _ _ (by omega), getD_take _ _ _ (by omega)]
        rcases Nat.eq_zero_or_pos (d.dom.exponents.getD m 0) with h | h
        · refine Or.inl ⟨h, ?_⟩
          simp only [hP] at hspec
          omega
        · refine Or.inr ⟨h, ?_⟩
          by_contra hc
          have hb : 0 < d.ran.exponents.getD m 0 := by omega
          rcases hred m hm2 h hb with hcon | hcon
          · exact absurd (hzeroA (m + 1) (le_refl _)) (by omega)
          · exact absurd (hzeroB (m + 1) (le_refl _)) (by omega)
      · -- the interior condition, inherited from reducedness
        intro k hk ha hb
        rw [hlA] at hk
        rw [getD_take _ _ _ (by omega)] at ha
        rw [getD_take _ _ _ (by omega)] at hb
        rcases hred k (by omega) ha hb with h | h
        · exact Or.inl (by rw [getD_take _ _ _ (by omega)]; exact h)
        · exact Or.inr (by rw [getD_take _ _ _ (by omega)]; exact h)
    · rw [hfeq, word_take hzeroA, word_take hzeroB]
  · -- both exponent lists are identically zero, so `f = 1`
    exfalso
    simp only [not_exists, hP, not_or, Nat.not_lt, Nat.le_zero] at hex
    have hsA : d.dom.exponents.sum = 0 :=
      sum_eq_zero_of_getD fun k _ => (hex k).1
    have hsB : d.ran.exponents.sum = 0 :=
      sum_eq_zero_of_getD fun k _ => (hex k).2
    rw [hfeq, word_eq, word_eq, wordFrom_of_sum_eq_zero _ hsA 0,
      wordFrom_of_sum_eq_zero _ hsB 0, inv_one, mul_one] at hne
    exact hne rfl
