-- Prove2me | solution 2 for BitcoinUniqueness.coinbase_height_prefix
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-29T15:12:32.410488+00:00
-- url     : https://prove2.me/submissions/93d813d3-d224-4685-a966-3382a0ea6839

import Definitions.Def_BitcoinUniqueness
import Theorems.Thm_BitcoinBlockV2_acceptance
import Theorems.Thm_BitcoinBlockV2_apply_spec
import Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
import Theorems.Thm_BitcoinScript_serialize_roundtrip
import Theorems.Thm_BitcoinSer_leBytes_length
import Theorems.Thm_BitcoinSer_readLE_leBytes

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

/-- An accepted block at a height where BIP34 is enforced has the height push as a prefix of its
coinbase `scriptSig`. -/
theorem solution (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hR : BitcoinBlockV2.Reachable S) (h : BitcoinBlockV2.validate S b now = .accept S' undo)
    (h34 : BitcoinHeader.BIP34Height ≤ S.nextHeight) :
    (BitcoinBlockV2.heightScript S.nextHeight).isPrefixOf (BitcoinUniqueness.coinbaseScriptSig b) = true := by
  have hV := (BitcoinBlockV2.acceptance S b now hR).1 ⟨S', undo, h⟩
  obtain ⟨-, hB, hC, -⟩ := hV
  have hact : BitcoinActivation.activeAfter S.tipHeight .heightInCB = true := by
    have hh : S.nextHeight = S.tipHeight + 1 := by
      simp only [ChainState.nextHeight, ChainState.tipHeight]
      have hne : S.headers ≠ [] := by
        have hwf := BitcoinBlockV2.reachable_wellFormed S hR
        obtain ⟨hhead, -⟩ := hwf
        intro e; rw [e] at hhead; cases hhead
      have := List.length_pos_iff.2 hne
      omega
    simp only [BitcoinActivation.activeAfter, BitcoinActivation.deploymentHeight]
    simp only [BitcoinHeader.BIP34Height] at h34
    exact decide_eq_true (by omega)
  have hpre := hC.2.1 hact
  -- the coinbase is the first transaction and has an input
  have hne : b.vtx ≠ [] := hB.1
  obtain ⟨cb, rest⟩ := b.vtx |> fun _ => (b.vtx, ())
  cases hv : b.vtx with
  | nil => exact absurd hv hne
  | cons cb rest =>
    have hcb : isCoinBase cb = true := hB.2.2.2.2.2.1 cb (by rw [hv]; simp)
    simp only [coinbaseScriptSig, hv, List.headD_cons]
    rw [hv] at hpre
    simp only [List.take_succ_cons, List.take_zero, List.mem_singleton, forall_eq] at hpre
    cases hvin : cb.vin with
    | nil => simp [isCoinBase, hvin] at hcb
    | cons i irest =>
      simp only [List.headD_cons]
      have := hpre i (by rw [hvin]; simp)
      exact this
