-- Prove2me | solution 1 for BitcoinUniqueness.chain_coinbases_distinct
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T14:02:41.394717+00:00
-- url     : https://prove2.me/submissions/85c7d531-db4f-4781-930b-4a5cd77ae79d

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinHeader
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinReorg
open BitcoinUniqueness BitcoinSer BitcoinBlockV2

theorem s229_validate_accept_inv {S : ChainState} {b : BitcoinSer.Block} {now : Int} {S' : ChainState}
    {undo : BlockUndo} (h : validate S b now = .accept S' undo) :
    contextualCheckBlock S b = true ∧ ∃ u, connectBlock S b = some (u, undo) ∧
      S' = ⟨S.headers ++ [b.header], u⟩ := by
  unfold validate at h
  split at h
  · by_cases h1 : checkBlock b = true
    · by_cases h2 : contextualCheckBlock S b = true
      · simp only [h1, h2, Bool.not_true, Bool.false_eq_true, if_false] at h
        refine ⟨h2, ?_⟩
        split at h
        · cases h
        · rename_i u un hc
          cases h
          exact ⟨u, hc, rfl⟩
      · simp [h1, h2] at h
    · simp [h1] at h
  · rename_i hne
    exact (hne _ _ h).elim

theorem s229_cb_prefix {S : ChainState} {b : BitcoinSer.Block} {now : Int} {S' : ChainState}
    {undo : BlockUndo} (h : BitcoinBlockV2.validate S b now = .accept S' undo)
    (h34 : BitcoinHeader.BIP34Height ≤ S.nextHeight) :
    (BitcoinBlockV2.heightScript S.nextHeight).isPrefixOf (BitcoinUniqueness.coinbaseScriptSig b) = true := by
  obtain ⟨hcc, _⟩ := s229_validate_accept_inv h
  have hact : BitcoinActivation.activeAfter S.tipHeight .heightInCB = true := by
    unfold BitcoinActivation.activeAfter ChainState.tipHeight
    unfold ChainState.nextHeight BitcoinHeader.BIP34Height at h34
    simp [BitcoinActivation.deploymentHeight]; omega
  unfold contextualCheckBlock at hcc
  simp only [hact, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hcc
  exact hcc.1.1.2

theorem s229_natBytes_len (k n : Nat) (h : n < 256 ^ k) : (BitcoinScript.natBytes n).length ≤ k := by
  induction k generalizing n with
  | zero =>
    have : n = 0 := by simp at h; omega
    subst this; rw [BitcoinScript.natBytes]; simp
  | succ k ih =>
    rw [BitcoinScript.natBytes]
    by_cases hn : n = 0
    · simp [hn]
    · simp only [hn, dite_false, List.length_cons]
      have : n / 256 < 256 ^ k := by
        rw [Nat.pow_succ'] at h
        exact Nat.div_lt_of_lt_mul h
      have := ih _ this
      omega

theorem s229_natBytes_ne (n : Nat) (h : n ≠ 0) : BitcoinScript.natBytes n ≠ [] := by
  rw [BitcoinScript.natBytes]; simp [h]

theorem s229_leNat_natBytes (n : Nat) : BitcoinScript.leNat (BitcoinScript.natBytes n) = n := by
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rw [BitcoinScript.natBytes]
    by_cases hn : n = 0
    · simp [hn, BitcoinScript.leNat]
    · simp only [hn, dite_false, BitcoinScript.leNat, BitVec.toNat_ofNat]
      rw [ih (n / 256) (Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by decide))]
      have e : n % 256 % (2^8) = n % 256 := Nat.mod_mod n 256
      rw [e]; omega

theorem s229_leNat_append0 (x : BitcoinSer.Bytes) : BitcoinScript.leNat (x ++ [0#8]) = BitcoinScript.leNat x := by
  induction x with
  | nil => simp [BitcoinScript.leNat]
  | cons b r ih => simp [BitcoinScript.leNat, ih]

theorem s229_serialize (n : Nat) (h0 : n ≠ 0) (h : n < 2 ^ 31) :
    BitcoinScript.leNat (BitcoinScript.serialize (n : Int)) = n ∧
    1 ≤ (BitcoinScript.serialize (n : Int)).length ∧ (BitcoinScript.serialize (n : Int)).length ≤ 5 := by
  have hl := s229_natBytes_len 4 n (by omega)
  have hne := s229_natBytes_ne n h0
  have hpos : 0 < (BitcoinScript.natBytes n).length := List.length_pos_iff.2 hne
  unfold BitcoinScript.serialize
  have hi : ((n : Int) = 0) = False := by simp; omega
  have hneg : ((n : Int) < 0) = False := by simp
  simp only [hi, hneg, if_false, Int.natAbs_natCast, decide_false]
  split
  · simp [s229_leNat_append0, s229_leNat_natBytes]; omega
  · simp [s229_leNat_natBytes]; omega

theorem s229_hs_cases (n : Nat) (h : n < 2 ^ 31) :
    (n = 0 ∧ heightScript n = [0#8]) ∨
    (1 ≤ n ∧ n ≤ 16 ∧ heightScript n = [BitVec.ofNat 8 (0x50 + n)]) ∨
    (16 < n ∧ heightScript n = BitVec.ofNat 8 (BitcoinScript.serialize (n : Int)).length ::
        BitcoinScript.serialize (n : Int) ∧
      1 ≤ (BitcoinScript.serialize (n : Int)).length ∧ (BitcoinScript.serialize (n : Int)).length ≤ 5 ∧
      BitcoinScript.leNat (BitcoinScript.serialize (n : Int)) = n) := by
  unfold heightScript
  by_cases h0 : n = 0
  · left; simp [h0]
  by_cases h16 : n ≤ 16
  · right; left; simp [h0, h16]; omega
  · right; right
    obtain ⟨e1, e2, e3⟩ := s229_serialize n h0 h
    refine ⟨by omega, ?_, e2, e3, e1⟩
    simp only [h0, h16, if_false]
    unfold BitcoinSig.pushBytes BitcoinSig.OP_PUSHDATA1
    rw [if_pos (by omega)]

theorem s229_hs_prefix (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (h : (BitcoinBlockV2.heightScript a).isPrefixOf (BitcoinBlockV2.heightScript b) = true) : a = b := by
  rw [List.isPrefixOf_iff_prefix] at h
  obtain ⟨t, ht⟩ := h
  rcases s229_hs_cases a ha with ⟨a0, ea⟩ | ⟨a1, a2, ea⟩ | ⟨a1, ea, la1, la2, va⟩ <;>
  rcases s229_hs_cases b hb with ⟨b0, eb⟩ | ⟨b1, b2, eb⟩ | ⟨b1, eb, lb1, lb2, vb⟩ <;>
  rw [ea, eb] at ht <;> simp only [List.cons_append, List.nil_append, List.cons.injEq] at ht
  all_goals first
    | omega
    | (obtain ⟨hb', hr⟩ := ht
       have hv := congrArg BitVec.toNat hb'
       simp only [BitVec.toNat_ofNat, Nat.reducePow, Nat.reduceMod] at hv
       first
       | omega
       | (have hlen : (BitcoinScript.serialize (a : Int)).length = (BitcoinScript.serialize (b : Int)).length := by omega
          have : t.length = 0 := by
            have := congrArg List.length hr
            simp at this; omega
          rw [List.length_eq_zero_iff] at this
          subst this
          simp only [List.append_nil] at hr
          rw [← va, ← vb, hr]))

theorem s229_ne {a b : Nat} {s₁ s₂ : BitcoinSer.Bytes} (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (hne : a ≠ b)
    (h₁ : (heightScript a).isPrefixOf s₁ = true) (h₂ : (heightScript b).isPrefixOf s₂ = true) : s₁ ≠ s₂ := by
  intro e
  subst e
  rw [List.isPrefixOf_iff_prefix] at h₁ h₂
  rcases List.prefix_or_prefix_of_prefix h₁ h₂ with h | h
  · exact hne (s229_hs_prefix a b ha hb (List.isPrefixOf_iff_prefix.2 h))
  · exact hne (s229_hs_prefix b a hb ha (List.isPrefixOf_iff_prefix.2 h)).symm

theorem s229_chain (bs : List (BitcoinSer.Block × Int)) : ∀ (S T : ChainState) (undos : List BlockUndo),
    BitcoinHeader.BIP34Height ≤ S.nextHeight →
    BitcoinReorg.connectChain S bs = some (T, undos) → S.nextHeight + bs.length < 2 ^ 31 →
    (∀ p ∈ bs, ∃ k, S.nextHeight ≤ k ∧ k < S.nextHeight + bs.length ∧
        (heightScript k).isPrefixOf (BitcoinUniqueness.coinbaseScriptSig p.1) = true) ∧
    (bs.map fun p => BitcoinUniqueness.coinbaseScriptSig p.1).Nodup := by
  induction bs with
  | nil => intro S T undos _ _ _; simp
  | cons p rest ih =>
    intro S T undos h34 hc hlt
    obtain ⟨b, now⟩ := p
    unfold BitcoinReorg.connectChain at hc
    split at hc
    · rename_i S' undo hv
      split at hc
      · cases hc
      · rename_i T' undos' hc'
        obtain ⟨_, u, _, hS'⟩ := s229_validate_accept_inv hv
        have hn : S'.nextHeight = S.nextHeight + 1 := by
          subst hS'; simp [ChainState.nextHeight]
        have hp := s229_cb_prefix hv h34
        obtain ⟨ih1, ih2⟩ := ih S' T' undos' (by omega) hc' (by simp at hlt; omega)
        simp only [List.length_cons] at hlt ⊢
        refine ⟨?_, ?_⟩
        · intro q hq
          rcases List.mem_cons.1 hq with e | hq
          · subst e; exact ⟨S.nextHeight, by omega, by omega, hp⟩
          · obtain ⟨k, hk1, hk2, hk3⟩ := ih1 q hq
            exact ⟨k, by omega, by omega, hk3⟩
        · rw [List.map_cons, List.nodup_cons]
          refine ⟨?_, ih2⟩
          intro hm
          rw [List.mem_map] at hm
          obtain ⟨q, hq, he⟩ := hm
          obtain ⟨k, hk1, hk2, hk3⟩ := ih1 q hq
          exact s229_ne (a := k) (b := S.nextHeight) (by omega) (by omega) (by omega) hk3 hp he
    · cases hc

theorem solution (S : ChainState) (hR : BitcoinBlockV2.Reachable S)
    (h34 : BitcoinHeader.BIP34Height ≤ S.nextHeight) (bs : List (BitcoinSer.Block × Int)) (T : ChainState)
    (undos : List BlockUndo) (hc : BitcoinReorg.connectChain S bs = some (T, undos))
    (hlt : S.nextHeight + bs.length < 2 ^ 31) :
    (bs.map fun p => BitcoinUniqueness.coinbaseScriptSig p.1).Nodup :=
  (s229_chain bs S T undos h34 hc hlt).2
