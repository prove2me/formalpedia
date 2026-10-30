-- Prove2me | solution 1 for BitcoinTapSoundnessV2.path_lands
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:06:24.101827+00:00
-- url     : https://prove2.me/submissions/189035f8-53e8-4d39-b0f6-69dfc06e584e

import Definitions.Def_BitcoinTapSoundnessV2
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinTapSoundnessV2_branch_eq
import Theorems.Thm_BitcoinTapSoundnessV2_leaf_ne_branch

open BitcoinTapSoundnessV2 BitcoinSer BitcoinTaproot

private theorem append_inj_len {α : Type} (a b c d : List α) (hl : a.length = c.length) (h : a ++ b = c ++ d) :
    a = c ∧ b = d :=
  List.append_inj h hl

private theorem tapleafHash_eq (v : Byte) (s : Bytes) : tapleafHash v s = tagged "TapLeaf" (leafMsg v s) := rfl

private theorem tapbranchHash_eq (a b : Bytes) : tapbranchHash a b = tagged "TapBranch" (branchMsg a b) := rfl

private theorem hash_length (T : TapTree) : T.hash.length = 32 := by
  cases T <;> simp [TapTree.hash, tapleafHash, tapbranchHash, tagged, BitcoinSig.taggedHash, BitcoinSer.sha256_length]

private theorem leaf_mem_leaves : ∀ (T : TapTree) (d : Nat) (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes),
    TapTree.leaf v s ∈ T.subtreesAt d → tapleafHash v s ∈ T.leaves
  | T, 0, v, s, h => by
    simp only [TapTree.subtreesAt, List.mem_singleton] at h
    subst h; simp [TapTree.leaves]
  | .leaf _ _, d + 1, v, s, h => by simp [TapTree.subtreesAt] at h
  | .branch l r, d + 1, v, s, h => by
    simp only [TapTree.subtreesAt, List.mem_append] at h
    simp only [TapTree.leaves, List.mem_append]
    rcases h with h | h
    · exact Or.inl (leaf_mem_leaves l d v s h)
    · exact Or.inr (leaf_mem_leaves r d v s h)

private theorem branch_children_mem : ∀ (T : TapTree) (d : Nat) (l r : TapTree),
    TapTree.branch l r ∈ T.subtreesAt d → l ∈ T.subtreesAt (d + 1) ∧ r ∈ T.subtreesAt (d + 1)
  | T, 0, l, r, h => by
    simp only [TapTree.subtreesAt, List.mem_singleton] at h
    subst h; simp [TapTree.subtreesAt]
  | .leaf _ _, d + 1, l, r, h => by simp [TapTree.subtreesAt] at h
  | .branch a b, d + 1, l, r, h => by
    simp only [TapTree.subtreesAt, List.mem_append] at h ⊢
    rcases h with h | h
    · have := branch_children_mem a d l r h; exact ⟨Or.inl this.1, Or.inl this.2⟩
    · have := branch_children_mem b d l r h; exact ⟨Or.inr this.1, Or.inr this.2⟩

private theorem path_lands_aux (T : TapTree) :
    ∀ (nodes : List BitcoinSer.Bytes) (h : BitcoinSer.Bytes), (∀ n ∈ nodes, n.length = 32) → h.length = 32 →
    nodes.foldl tapbranchHash h = T.hash →
    (∃ U, walk T nodes h = .inl U ∧ U ∈ T.subtreesAt nodes.length ∧ U.hash = h) ∨
      (∃ x y, walk T nodes h = .inr (x, y) ∧ Collides x y)
  | [], h, _, _, heq => Or.inl ⟨T, rfl, by simp [TapTree.subtreesAt], heq.symm⟩
  | n :: rest, h, hn, hh, heq => by
    simp only [List.foldl_cons] at heq
    have hn' : ∀ m ∈ rest, m.length = 32 := fun m hm => hn m (List.mem_cons_of_mem _ hm)
    have hbl : (tapbranchHash h n).length = 32 := by
      simp [tapbranchHash, tagged, BitcoinSig.taggedHash, BitcoinSer.sha256_length]
    rcases path_lands_aux T rest _ hn' hbl heq with ⟨U, hw, hU, hUh⟩ | ⟨x, y, hw, hc⟩
    · cases U with
      | leaf v s =>
        right
        refine ⟨_, _, ?_, BitcoinTapSoundnessV2.leaf_ne_branch v s h n hUh⟩
        simp only [walk, hw]
      | branch l r =>
        simp only [TapTree.hash] at hUh
        obtain ⟨hl, hr⟩ := branch_children_mem T rest.length l r hU
        by_cases hl' : h = l.hash
        · left
          refine ⟨l, ?_, by simpa [List.length_cons] using hl, hl'.symm⟩
          simp only [walk, hw]; rw [if_pos hl']
        · by_cases hr' : h = r.hash
          · left
            refine ⟨r, ?_, by simpa [List.length_cons] using hr, hr'.symm⟩
            simp only [walk, hw]; rw [if_neg hl', if_pos hr']
          · rcases BitcoinTapSoundnessV2.branch_eq _ _ _ _ (hash_length l) (hash_length r) hh (hn n (List.mem_cons_self ..)) hUh
              with ⟨⟨h1, -⟩ | ⟨-, h2⟩⟩ | hc
            · exact absurd h1.symm hl'
            · exact absurd h2.symm hr'
            · right
              refine ⟨_, _, ?_, hc⟩
              simp only [walk, hw]; rw [if_neg hl', if_neg hr']
    · right
      refine ⟨x, y, ?_, hc⟩
      simp only [walk, hw]

/-- **Walking a Merkle path.** Following a path of 32-byte nodes from a 32-byte hash `h` to the
root of `T`, `walk` either lands on a subtree of `T` at the path's depth whose hash is `h`, or
returns two colliding strings. -/
theorem solution (T : BitcoinTapSoundnessV2.TapTree) (nodes : List BitcoinSer.Bytes) (h : BitcoinSer.Bytes)
    (hn : ∀ n ∈ nodes, n.length = 32) (hh : h.length = 32) (heq : nodes.foldl BitcoinTaproot.tapbranchHash h = T.hash) :
    (∃ U, BitcoinTapSoundnessV2.walk T nodes h = .inl U ∧ U ∈ T.subtreesAt nodes.length ∧ U.hash = h) ∨
      (∃ x y, BitcoinTapSoundnessV2.walk T nodes h = .inr (x, y) ∧ BitcoinTapSoundnessV2.Collides x y) :=
  path_lands_aux T nodes h hn hh heq
