-- Prove2me | solution 2 for BitcoinUniqueness.chain_coinbases_distinct
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:14:01.893612+00:00
-- url     : https://prove2.me/submissions/5271a890-3478-4315-98b3-cf8f9c241eab

import Definitions.Def_BitcoinUniqueness
import Theorems.Thm_BitcoinBlockV2_acceptance
import Theorems.Thm_BitcoinBlockV2_apply_spec
import Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinSer_leBytes_length
import Theorems.Thm_BitcoinSer_readLE_leBytes
import Theorems.Thm_BitcoinUniqueness_coinbases_distinct

open BitcoinUniqueness BitcoinSer BitcoinBlockV2

private theorem leBytes_inj (k a b : Nat) (ha : a < 2 ^ (8 * k)) (hb : b < 2 ^ (8 * k))
    (h : BitcoinSer.leBytes k a = BitcoinSer.leBytes k b) : a = b := by
  have h1 := BitcoinSer.readLE_leBytes k a [] ha
  have h2 := BitcoinSer.readLE_leBytes k b [] hb
  rw [h] at h1; rw [h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact h2.1

private theorem ofNat8_inj (a b : Nat) (ha : a < 256) (hb : b < 256) (h : BitVec.ofNat 8 a = BitVec.ofNat 8 b) : a = b := by
  have := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at this
  rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] at this

private theorem natBytes_length : ∀ (k n : Nat), n < 256 ^ k → (BitcoinScript.natBytes n).length ≤ k
  | 0, n, h => by
    have : n = 0 := by simp at h; omega
    subst this; simp [BitcoinScript.natBytes]
  | k + 1, n, h => by
    unfold BitcoinScript.natBytes
    split
    · simp
    · simp only [List.length_cons]
      have := natBytes_length k (n / 256) (by
        rw [Nat.pow_succ] at h
        exact Nat.div_lt_of_lt_mul (by rw [Nat.mul_comm]; exact h))
      omega

private theorem setTop_length : ∀ (l : BitcoinSer.Bytes), (BitcoinScript.setTop l).length = l.length
  | [] => rfl
  | [b] => rfl
  | b :: c :: s => by simp [BitcoinScript.setTop, setTop_length (c :: s)]

private theorem serialize_length (n : Nat) (hn : n < 2 ^ 32) : (BitcoinScript.serialize n).length ≤ 5 := by
  unfold BitcoinScript.serialize
  split
  · simp
  · simp only [Int.natAbs_natCast]
    have e4 : (256:Nat)^4 = 2^32 := by rfl
    have hl := natBytes_length 4 n (by omega)
    split
    · simp only [List.length_append, List.length_singleton]; omega
    · split
      · rw [setTop_length]; omega
      · omega

private theorem serialize_inj (a b : Nat) (h : BitcoinScript.serialize a = BitcoinScript.serialize b) : a = b := by
  have ha := BitcoinScript.serialize_roundtrip (a : Int)
  have hb := BitcoinScript.serialize_roundtrip (b : Int)
  rw [h] at ha; rw [ha] at hb
  exact Int.ofNat.inj hb

private theorem serialize_pos_nonempty (n : Nat) (hn : 0 < n) : BitcoinScript.serialize n ≠ [] := by
  intro h
  have := BitcoinScript.serialize_roundtrip (n : Int)
  rw [h] at this
  simp [BitcoinScript.setVch, BitcoinScript.leNat, BitcoinScript.topBit] at this
  omega

/-- The shape of a push of a non-empty element: a first byte in `1..0x4e` and at least as many
further bytes as the element. -/
private theorem pushBytes_shape (d : BitcoinSer.Bytes) (hne : d ≠ []) (hd : d.length < 2 ^ 32) :
    ∃ c rest, BitcoinSig.pushBytes d = c :: rest ∧ 1 ≤ c.toNat ∧ c.toNat ≤ 0x4e ∧ d.length ≤ rest.length := by
  have hpos : 0 < d.length := List.length_pos_iff.2 hne
  unfold BitcoinSig.pushBytes
  simp only [BitcoinSig.OP_PUSHDATA1, BitcoinSig.OP_PUSHDATA2, BitcoinSig.OP_PUSHDATA4]
  by_cases c1 : d.length < 76
  · simp only [c1, ite_true]
    refine ⟨_, d, rfl, ?_, ?_, Nat.le_refl _⟩ <;> simp only [BitVec.toNat_ofNat] <;> omega
  · simp only [c1, ite_false]
    by_cases c2 : d.length ≤ 255
    · simp only [c2, ite_true]
      refine ⟨_, _, rfl, ?_, ?_, by simp⟩ <;> simp only [BitVec.toNat_ofNat] <;> omega
    · simp only [c2, ite_false]
      by_cases c3 : d.length ≤ 65535
      · simp only [c3, ite_true]
        refine ⟨_, _, rfl, by decide, by decide, ?_⟩
        show d.length ≤ (BitcoinSer.leBytes 2 d.length ++ d).length
        rw [List.length_append, BitcoinSer.leBytes_length]; omega
      · simp only [c3, ite_false]
        refine ⟨_, _, rfl, by decide, by decide, ?_⟩
        show d.length ≤ (BitcoinSer.leBytes 4 d.length ++ d).length
        rw [List.length_append, BitcoinSer.leBytes_length]; omega

/-- A single byte `0` or `0x50 + n` (`n ≤ 16`) is never a prefix of a push, and a push is never a
prefix of a single byte. -/
private theorem single_push_no_prefix (x : BitcoinSer.Byte) (hx : x.toNat = 0 ∨ 0x51 ≤ x.toNat) (d : BitcoinSer.Bytes)
    (hne : d ≠ []) (hd : d.length < 2 ^ 32) :
    [x].isPrefixOf (BitcoinSig.pushBytes d) = false ∧ (BitcoinSig.pushBytes d).isPrefixOf [x] = false := by
  obtain ⟨c, rest, hp, h1, h2, h3⟩ := pushBytes_shape d hne hd
  rw [hp]
  constructor
  · apply Bool.eq_false_iff.2; intro h
    rw [List.isPrefixOf_iff_prefix, List.cons_prefix_cons] at h
    rw [h.1] at hx; omega
  · apply Bool.eq_false_iff.2; intro h
    rw [List.isPrefixOf_iff_prefix, List.cons_prefix_cons] at h
    have := List.IsPrefix.length_le h.2
    have hpos : 0 < d.length := List.length_pos_iff.2 hne
    simp only [List.length_nil] at this; omega

/-- Along a chain connected to a reachable state at or above the BIP34 height (and below `2^31`),
the coinbase `scriptSig`s of distinct blocks are pairwise distinct: no two post-BIP34 blocks of
one chain share a coinbase. -/
theorem solution (S : ChainState) (hR : BitcoinBlockV2.Reachable S)
    (h34 : BitcoinHeader.BIP34Height ≤ S.nextHeight) (bs : List (BitcoinSer.Block × Int)) (T : ChainState)
    (undos : List BlockUndo) (hc : BitcoinReorg.connectChain S bs = some (T, undos))
    (hlt : S.nextHeight + bs.length < 2 ^ 31) :
    (bs.map fun p => BitcoinUniqueness.coinbaseScriptSig p.1).Nodup := by
  -- generalize: each block of `bs` is accepted at height `S.nextHeight + i`
  suffices H : ∀ (bs : List (BitcoinSer.Block × Int)) (S : ChainState), BitcoinBlockV2.Reachable S →
      BitcoinHeader.BIP34Height ≤ S.nextHeight → S.nextHeight + bs.length < 2 ^ 31 →
      (∃ T undos, BitcoinReorg.connectChain S bs = some (T, undos)) →
      (bs.map fun p => BitcoinUniqueness.coinbaseScriptSig p.1).Nodup ∧
      ∀ p ∈ bs, ∀ (T' : ChainState) (u : BlockUndo) (S₀ : ChainState), BitcoinBlockV2.Reachable S₀ →
        BitcoinBlockV2.validate S₀ p.1 p.2 = .accept T' u → S.nextHeight ≤ S₀.nextHeight → S₀.nextHeight < 2 ^ 31 →
        BitcoinHeader.BIP34Height ≤ S₀.nextHeight → True from
    (H bs S hR h34 hlt ⟨T, undos, hc⟩).1
  intro bs
  induction bs with
  | nil => intro S _ _ _ _; exact ⟨List.nodup_nil, fun p hp => absurd hp (List.not_mem_nil)⟩
  | cons p rest ih =>
    intro S hR h34 hlt hc
    obtain ⟨T, undos, hc⟩ := hc
    obtain ⟨b, now⟩ := p
    simp only [BitcoinReorg.connectChain] at hc
    cases hv : validate S b now with
    | accept S1 undo1 =>
      rw [hv] at hc; dsimp only at hc
      cases hc1 : BitcoinReorg.connectChain S1 rest with
      | none => rw [hc1] at hc; cases hc
      | some q =>
        have hR1 : Reachable S1 := Reachable.step hR hv
        have hS1 := BitcoinBlockV2.apply_spec S b now S1 undo1 hv
        have hn1 : S1.nextHeight = S.nextHeight + 1 := by
          subst hS1; simp only [applySpec, ChainState.nextHeight]; split <;> simp
        simp only [List.length_cons] at hlt
        obtain ⟨hnd, -⟩ := ih S1 hR1 (by omega) (by omega) ⟨q.1, q.2, hc1⟩
        refine ⟨?_, fun _ _ _ _ _ _ _ _ _ _ => trivial⟩
        simp only [List.map_cons, List.nodup_cons]
        refine ⟨?_, hnd⟩
        -- the first block's coinbase differs from every later block's: later blocks sit at greater heights
        intro hmem
        obtain ⟨p', hp', heq⟩ := List.mem_map.1 hmem
        -- every later block is accepted at a height ≥ S.nextHeight + 1 from a reachable state
        have hlater : ∀ (rest : List (BitcoinSer.Block × Int)) (S1 : ChainState), Reachable S1 →
            (∃ T undos, BitcoinReorg.connectChain S1 rest = some (T, undos)) → ∀ p' ∈ rest,
            ∃ (S₀ : ChainState) (T' : ChainState) (u : BlockUndo), Reachable S₀ ∧ S1.nextHeight ≤ S₀.nextHeight ∧
              S₀.nextHeight + 1 ≤ S1.nextHeight + rest.length ∧
              validate S₀ p'.1 p'.2 = .accept T' u := by
          intro rest
          induction rest with
          | nil => intro _ _ _ p' hp'; exact absurd hp' List.not_mem_nil
          | cons q' r' ih' =>
            intro S1 hR1 hc p' hp'
            obtain ⟨T, undos, hc⟩ := hc
            obtain ⟨b', now'⟩ := q'
            simp only [BitcoinReorg.connectChain] at hc
            cases hv' : validate S1 b' now' with
            | accept S2 undo2 =>
              rw [hv'] at hc; dsimp only at hc
              cases hc2 : BitcoinReorg.connectChain S2 r' with
              | none => rw [hc2] at hc; cases hc
              | some q2 =>
                have hS2 := BitcoinBlockV2.apply_spec S1 b' now' S2 undo2 hv'
                have hn2 : S2.nextHeight = S1.nextHeight + 1 := by
                  subst hS2; simp only [applySpec, ChainState.nextHeight]; split <;> simp
                simp only [List.mem_cons] at hp'
                rcases hp' with hp' | hp'
                · subst hp'; exact ⟨S1, S2, undo2, hR1, Nat.le_refl _, by simp only [List.length_cons]; omega, hv'⟩
                · obtain ⟨S₀, T', u, hR0, hle, hlt', hv0⟩ := ih' S2 (Reachable.step hR1 hv') ⟨q2.1, q2.2, hc2⟩ p' hp'
                  exact ⟨S₀, T', u, hR0, by omega, by simp only [List.length_cons]; omega, hv0⟩
            | invalid => rw [hv'] at hc; cases hc
            | futureTime => rw [hv'] at hc; cases hc
            | missingPrev => rw [hv'] at hc; cases hc
        obtain ⟨S₀, T', u, hR0, hle, hlt', hv0⟩ := hlater rest S1 hR1 ⟨q.1, q.2, hc1⟩ p' hp'
        exact BitcoinUniqueness.coinbases_distinct S S₀ b p'.1 now p'.2 S1 T' undo1 u hR hR0 hv hv0 h34
          (by omega) (by omega) (by omega) (by omega) heq.symm
    | invalid => rw [hv] at hc; cases hc
    | futureTime => rw [hv] at hc; cases hc
    | missingPrev => rw [hv] at hc; cases hc
