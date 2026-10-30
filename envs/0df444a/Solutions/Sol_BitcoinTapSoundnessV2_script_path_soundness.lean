-- Prove2me | solution 1 for BitcoinTapSoundnessV2.script_path_soundness
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:06:44.490027+00:00
-- url     : https://prove2.me/submissions/53b1eca9-6c77-4c09-a4e9-61345aecde88

import Definitions.Def_BitcoinTapSoundnessV2
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinTapSoundnessV2_branch_eq
import Theorems.Thm_BitcoinTapSoundnessV2_leaf_ne_branch
import Theorems.Thm_BitcoinTapSoundnessV2_path_lands

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

/-- The path nodes of a well-sized control block are 32 bytes each. -/
private theorem controlNodes_len (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = TAPROOT_CONTROL_BASE_SIZE + TAPROOT_CONTROL_NODE_SIZE * k) :
    ∀ n ∈ controlNodes control, n.length = 32 := by
  simp only [controlNodes, TAPROOT_CONTROL_BASE_SIZE, TAPROOT_CONTROL_NODE_SIZE] at hc ⊢
  have hk : (control.length - 33) / 32 = k := by rw [hc]; omega
  rw [hk]
  have hlen : (control.drop 33).length = 32 * k := by simp [List.length_drop, hc]
  generalize control.drop 33 = s at hlen
  clear hc hk
  induction k generalizing s with
  | zero => intro n hn; simp [controlNodes.go] at hn
  | succ k ih =>
    intro n hn
    simp only [controlNodes.go, List.mem_cons] at hn
    rcases hn with hn | hn
    · subst hn; simp only [List.length_take, hlen, TAPROOT_CONTROL_NODE_SIZE]; omega
    · exact ih (s.drop 32) (by simp only [List.length_drop, hlen, TAPROOT_CONTROL_NODE_SIZE]; omega) n hn

/-- **Script-path soundness (Merkle level).** A control block whose Merkle path carries the leaf
hash of `(v, s)` to the root of `T` opens a leaf of `T` (and `scriptPathWitness` is `none`), or
`scriptPathWitness` names two colliding strings. -/
theorem solution (T : BitcoinTapSoundnessV2.TapTree) (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) = T.hash) :
    (BitcoinTapSoundnessV2.scriptPathWitness T control v s = none ∧ BitcoinTaproot.tapleafHash v s ∈ T.leaves) ∨
      (∃ x y, BitcoinTapSoundnessV2.scriptPathWitness T control v s = some (x, y) ∧ BitcoinTapSoundnessV2.Collides x y) := by
  simp only [taprootMerkleRoot] at h
  have hl : (tapleafHash v s).length = 32 := by simp [tapleafHash, tagged, BitcoinSig.taggedHash, BitcoinSer.sha256_length]
  unfold scriptPathWitness
  rcases BitcoinTapSoundnessV2.path_lands T (controlNodes control) _ (controlNodes_len control k hc) hl h
    with ⟨U, hw, hU, hUh⟩ | ⟨x, y, hw, hcol⟩
  · rw [hw]
    cases U with
    | leaf v' s' =>
      left
      simp only [TapTree.hash] at hUh
      refine ⟨rfl, ?_⟩
      rw [← hUh]; exact leaf_mem_leaves T _ v' s' hU
    | branch l r =>
      right
      simp only [TapTree.hash] at hUh
      exact ⟨_, _, rfl, BitcoinTapSoundnessV2.leaf_ne_branch v s _ _ hUh.symm⟩
  · rw [hw]; exact Or.inr ⟨x, y, rfl, hcol⟩
