-- Prove2me | solution 1 for BitcoinTapSoundnessV2.commitment_soundness
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T18:07:10.882531+00:00
-- url     : https://prove2.me/submissions/50fbc2ce-108f-41be-af4c-d68369b0d7f2

import Definitions.Def_BitcoinTapSoundnessV2
import Theorems.Thm_BitcoinSer_sha256_length
import Theorems.Thm_BitcoinTapSoundnessV2_branch_eq
import Theorems.Thm_BitcoinTapSoundnessV2_leaf_ne_branch
import Theorems.Thm_BitcoinTapSoundnessV2_script_path_soundness
import Theorems.Thm_BitcoinTapSoundnessV2_tagged_collision

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

private theorem tapTweakHash_length (a b : Bytes) : (tapTweakHash a b).length = 32 := by
  simp [tapTweakHash, tagged, BitcoinSig.taggedHash, BitcoinSer.sha256_length]

/-- **Script-path soundness (commitment level).** If an output key `q` was honestly built from an
internal key and a tree `T`, then a control block with that internal key and parity that passes
`VerifyTaprootCommitment` for the leaf `(v, s)` either (1) has the tree's root as its Merkle root and
opens a leaf of `T` or names two colliding strings through `scriptPathWitness`; or (2) has a different
root but the same tweak hash, so the two `TapTweak` preimages collide; or (3) has a different root and
a different tweak, and the two 32-byte tweaks both carry the internal point to `q`. -/
theorem solution (q internal32 : BitcoinSer.Bytes) (parity : Bool)
    (T : BitcoinTapSoundnessV2.TapTree) (hT : BitcoinTapSoundnessV2.HonestOutput q internal32 parity T)
    (control : BitcoinSer.Bytes) (k : Nat)
    (hc : control.length = BitcoinTaproot.TAPROOT_CONTROL_BASE_SIZE + BitcoinTaproot.TAPROOT_CONTROL_NODE_SIZE * k)
    (hkey : BitcoinTapSoundnessV2.controlInternalKey control = internal32) (hpar : BitcoinTapSoundnessV2.controlParity control = parity)
    (v : BitcoinSer.Byte) (s : BitcoinSer.Bytes)
    (h : BitcoinTaproot.verifyTaprootCommitment control q (BitcoinTaproot.tapleafHash v s) = true) :
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) = T.hash ∧
      ((BitcoinTapSoundnessV2.scriptPathWitness T control v s = none ∧ BitcoinTaproot.tapleafHash v s ∈ T.leaves) ∨
        (∃ x y, BitcoinTapSoundnessV2.scriptPathWitness T control v s = some (x, y) ∧ BitcoinTapSoundnessV2.Collides x y))) ∨
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) ≠ T.hash ∧
      BitcoinTapSoundnessV2.Collides
        (BitcoinTapSoundnessV2.taggedPre "TapTweak" (internal32 ++ BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s)))
        (BitcoinTapSoundnessV2.taggedPre "TapTweak" (internal32 ++ T.hash))) ∨
    (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s) ≠ T.hash ∧
      ∃ P, BitcoinSig.liftX (BitcoinSig.beVal internal32) = some P ∧
        BitcoinTapSoundnessV2.TweakCollision q parity P
          (BitcoinTaproot.tapTweakHash internal32 (BitcoinTaproot.taprootMerkleRoot control (BitcoinTaproot.tapleafHash v s)))
          (BitcoinTaproot.tapTweakHash internal32 T.hash)) := by
  simp only [verifyTaprootCommitment] at h
  rw [show (control.drop 1).take 32 = internal32 from hkey] at h
  rw [show decide ((control.getD 0 0).toNat % 2 = 1) = parity from hpar] at h
  simp only [HonestOutput, checkTapTweak] at hT h
  cases hP : BitcoinSig.liftX (BitcoinSig.beVal internal32) with
  | none => rw [hP] at hT; cases hT
  | some P =>
    rw [hP] at hT h
    by_cases hroot : taprootMerkleRoot control (tapleafHash v s) = T.hash
    · exact Or.inl ⟨hroot, BitcoinTapSoundnessV2.script_path_soundness T control k hc v s hroot⟩
    · by_cases htw : tapTweakHash internal32 (taprootMerkleRoot control (tapleafHash v s)) = tapTweakHash internal32 T.hash
      · simp only [tapTweakHash] at htw
        rcases BitcoinTapSoundnessV2.tagged_collision _ _ _ _ htw with ⟨-, hm⟩ | hcol
        · exfalso; apply hroot
          exact (append_inj_len _ _ _ _ rfl hm).2
        · exact Or.inr (Or.inl ⟨hroot, hcol⟩)
      · exact Or.inr (Or.inr ⟨hroot, P, rfl, htw, tapTweakHash_length _ _, tapTweakHash_length _ _, h, hT⟩)
