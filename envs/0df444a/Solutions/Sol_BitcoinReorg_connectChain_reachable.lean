-- Prove2me | solution 1 for BitcoinReorg.connectChain_reachable
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T02:40:18.350552+00:00
-- url     : https://prove2.me/submissions/57043b24-8996-451a-b57d-54106ef17a7a

import Definitions.Def_BitcoinReorg
import Definitions.Def_BitcoinSer
open BitcoinReorg BitcoinBlockV2

namespace BtcAux
open BitcoinSer

theorem getCoin_spendCoin (u : Ledger) (op q : OutPoint) :
    getCoin (spendCoin u op) q = if q = op then none else getCoin u q := by
  induction u with
  | nil => simp [spendCoin, getCoin]
  | cons p rest ih =>
    obtain ⟨k, c⟩ := p
    by_cases hk : k = op
    · subst hk
      by_cases hq : q = k
      · subst hq; simp [spendCoin, ih]
      · have : ¬ k = q := fun h => hq h.symm
        simp [spendCoin, getCoin, ih, hq, this]
    · by_cases hq : q = op
      · subst hq
        have : ¬ k = q := hk
        simp [spendCoin, getCoin, ih, hk, this]
      · simp only [spendCoin, hk, if_false, getCoin, ih, hq]

theorem equiv_spendCoin {u v : Ledger} (h : Equiv u v) (op : OutPoint) :
    Equiv (spendCoin u op) (spendCoin v op) := by
  intro q; rw [getCoin_spendCoin, getCoin_spendCoin, h q]

theorem getCoin_addCoin (u : Ledger) (op : OutPoint) (c : Coin) (q : OutPoint) :
    getCoin (addCoin u op c) q =
      if isUnspendable c.out.scriptPubKey then getCoin u q
      else if q = op then some c else getCoin (spendCoin u op) q := by
  unfold addCoin
  by_cases hu : isUnspendable c.out.scriptPubKey
  · simp [hu]
  · by_cases hq : q = op
    · subst hq; simp [hu, getCoin]
    · have : ¬ op = q := fun h => hq h.symm
      simp [hu, getCoin, hq, this]

theorem equiv_addCoin {u v : Ledger} (h : Equiv u v) (op : OutPoint) (c : Coin) :
    Equiv (addCoin u op c) (addCoin v op c) := by
  intro q
  rw [getCoin_addCoin, getCoin_addCoin, h q, equiv_spendCoin h op q]

theorem equiv_addCoinsFrom (txid : Bytes) (height : Nat) (cb : Bool) (outs : List TxOut) :
    ∀ (u v : Ledger) (i : Nat), Equiv u v →
      Equiv (addCoinsFrom txid height cb u i outs) (addCoinsFrom txid height cb v i outs) := by
  induction outs with
  | nil => intro u v i h; simpa [addCoinsFrom] using h
  | cons o rest ih =>
    intro u v i h
    simp only [addCoinsFrom]
    exact ih _ _ _ (equiv_addCoin h _ _)

theorem equiv_spendInputs (ins : List TxIn) :
    ∀ (u v : Ledger), Equiv u v → Equiv (spendInputs u ins) (spendInputs v ins) := by
  induction ins with
  | nil => intro u v h; simpa [spendInputs] using h
  | cons i rest ih =>
    intro u v h
    simp only [spendInputs]
    exact ih _ _ (equiv_spendCoin h _)

theorem equiv_updateCoins {u v : Ledger} (h : Equiv u v) (tx : Tx) (H : Nat) :
    Equiv (updateCoins u tx H) (updateCoins v tx H) := by
  unfold updateCoins
  apply equiv_addCoinsFrom
  by_cases hc : isCoinBase tx = true
  · rw [if_pos hc, if_pos hc]; exact h
  · rw [if_neg hc, if_neg hc]; exact equiv_spendInputs _ _ _ h

end BtcAux


namespace BtcAux
open BitcoinSer


theorem haveCoin_eq {u v : Ledger} (h : Equiv u v) (op : OutPoint) : haveCoin u op = haveCoin v op := by
  simp only [haveCoin, h op]

theorem accessCoin_eq {u v : Ledger} (h : Equiv u v) (op : OutPoint) : accessCoin u op = accessCoin v op := by
  simp only [accessCoin, h op]

theorem inputsLoop_eq {u v : Ledger} (h : Equiv u v) (sh : Nat) (ins : List TxIn) :
    ∀ acc, inputsLoop u sh ins acc = inputsLoop v sh ins acc := by
  induction ins with
  | nil => intro acc; rfl
  | cons i rest ih => intro acc; simp only [inputsLoop, h i.prevout, ih]

theorem checkTxInputs_eq {u v : Ledger} (h : Equiv u v) (tx : Tx) (sh : Nat) :
    checkTxInputs u tx sh = checkTxInputs v tx sh := by
  simp only [checkTxInputs, haveCoin_eq h, inputsLoop_eq h]

theorem txSigOpCost_eq {u v : Ledger} (h : Equiv u v) (f : BitcoinActivation.ScriptFlags) (tx : Tx) :
    txSigOpCost f u tx = txSigOpCost f v tx := by
  simp only [txSigOpCost, accessCoin_eq h]

theorem sequenceLocksOk_eq {u v : Ledger} (h : Equiv u v) (height : Nat) (mtp : Nat → Nat) (lf : Nat) (tx : Tx) :
    sequenceLocksOk u height mtp lf tx = sequenceLocksOk v height mtp lf tx := by
  simp only [sequenceLocksOk, accessCoin_eq h]

theorem inputScriptsOk_eq {u v : Ledger} (h : Equiv u v) (f : BitcoinActivation.ScriptFlags) (tx : Tx) :
    inputScriptsOk f u tx = inputScriptsOk f v tx := by
  simp only [inputScriptsOk, accessCoin_eq h]

theorem txUndo_eq {u v : Ledger} (h : Equiv u v) (tx : Tx) : txUndo u tx = txUndo v tx := by
  simp only [txUndo, accessCoin_eq h]

def LRel (a b : Option LoopState) : Prop :=
  (a = none ∧ b = none) ∨
  ∃ x y, a = some x ∧ b = some y ∧ x.fees = y.fees ∧ x.sigOps = y.sigOps ∧ x.undo = y.undo ∧ Equiv x.utxo y.utxo

theorem connectLoop_equiv (f : BitcoinActivation.ScriptFlags) (height : Nat) (mtp : Nat → Nat) (lf : Nat)
    (txs : List Tx) :
    ∀ (u v : Ledger) (fees : Int) (sigOps : Nat) (undo : BlockUndo), Equiv u v →
      LRel (connectLoop f height mtp lf ⟨u, fees, sigOps, undo⟩ txs)
           (connectLoop f height mtp lf ⟨v, fees, sigOps, undo⟩ txs) := by
  induction txs with
  | nil =>
    intro u v fees sigOps undo h
    right; exact ⟨_, _, rfl, rfl, rfl, rfl, rfl, h⟩
  | cons tx rest ih =>
    intro u v fees sigOps undo h
    simp only [connectLoop, checkTxInputs_eq h, sequenceLocksOk_eq h, txUndo_eq h, txSigOpCost_eq h,
      inputScriptsOk_eq h]
    generalize (if isCoinBase tx = true then some (fees, undo) else
        match checkTxInputs v tx height with
        | none => none
        | some fee =>
          if (!moneyRange (fees + fee)) = true then none
          else
            if (!sequenceLocksOk v height mtp lf tx) = true then none
            else some (fees + fee, undo ++ [txUndo v tx])) = s
    cases s with
    | none => left; exact ⟨rfl, rfl⟩
    | some p =>
      obtain ⟨fees', undo'⟩ := p
      simp only []
      by_cases c1 : MAX_BLOCK_SIGOPS_COST < sigOps + txSigOpCost f v tx
      · rw [if_pos c1, if_pos c1]; left; exact ⟨rfl, rfl⟩
      · rw [if_neg c1, if_neg c1]
        by_cases c2 : (!isCoinBase tx && !inputScriptsOk f v tx) = true
        · rw [if_pos c2, if_pos c2]; left; exact ⟨rfl, rfl⟩
        · rw [if_neg c2, if_neg c2]
          exact ih _ _ _ _ _ (equiv_updateCoins h tx height)

theorem bip30Ok_eq {u v : Ledger} (h : Equiv u v) (b : Block) : bip30Ok u b = bip30Ok v b := by
  simp only [bip30Ok, haveCoin_eq h]

theorem connectBlock_equiv' (H : List Header) (u v : Ledger) (h : Equiv u v) (b : Block) :
    (connectBlock ⟨H, u⟩ b = none ∧ connectBlock ⟨H, v⟩ b = none) ∨
    (∃ u' v' undo, connectBlock ⟨H, u⟩ b = some (u', undo) ∧
      connectBlock ⟨H, v⟩ b = some (v', undo) ∧ Equiv u' v') := by
  have e1 : ∀ n hh, bip30Checked ⟨H, u⟩ n hh = bip30Checked ⟨H, v⟩ n hh := fun _ _ => rfl
  have e2 : ChainState.nextHeight ⟨H, u⟩ = ChainState.nextHeight ⟨H, v⟩ := rfl
  have e3 : ChainState.mtpNat ⟨H, u⟩ = ChainState.mtpNat ⟨H, v⟩ := rfl
  unfold connectBlock
  simp only [bip30Ok_eq h, e1, e2, e3]
  by_cases hg : headerHash b.header = genesisHash
  · simp only [hg, if_true]
    right; exact ⟨_, _, _, rfl, rfl, h⟩
  · simp only [hg, if_false]
    by_cases hb : (bip30Checked ⟨H, v⟩ (ChainState.nextHeight ⟨H, v⟩) (headerHash b.header) && !bip30Ok v b) = true
    · rw [if_pos hb, if_pos hb]; left; exact ⟨rfl, rfl⟩
    · rw [if_neg hb, if_neg hb]
      have key := connectLoop_equiv (BitcoinActivation.blockScriptFlags (ChainState.nextHeight ⟨H, v⟩) (scriptException (headerHash b.header)))
        (ChainState.nextHeight ⟨H, v⟩) (ChainState.mtpNat ⟨H, v⟩) (BitcoinActivation.lockTimeFlags (ChainState.nextHeight ⟨H, v⟩))
        b.vtx u v 0 0 [] h
      generalize connectLoop (BitcoinActivation.blockScriptFlags (ChainState.nextHeight ⟨H, v⟩) (scriptException (headerHash b.header)))
        (ChainState.nextHeight ⟨H, v⟩) (ChainState.mtpNat ⟨H, v⟩) (BitcoinActivation.lockTimeFlags (ChainState.nextHeight ⟨H, v⟩))
        ⟨u, 0, 0, []⟩ b.vtx = A at key ⊢
      generalize connectLoop (BitcoinActivation.blockScriptFlags (ChainState.nextHeight ⟨H, v⟩) (scriptException (headerHash b.header)))
        (ChainState.nextHeight ⟨H, v⟩) (ChainState.mtpNat ⟨H, v⟩) (BitcoinActivation.lockTimeFlags (ChainState.nextHeight ⟨H, v⟩))
        ⟨v, 0, 0, []⟩ b.vtx = B at key ⊢
      rcases key with ⟨ha, hb2⟩ | ⟨x, y, hx, hy, hf, hs, hu, he⟩
      · subst ha; subst hb2; left; exact ⟨rfl, rfl⟩
      · subst hx; subst hy
        simp only []
        rw [hf]
        by_cases c : valueOut (b.vtx.headD genesisCoinbase) >
            y.fees + ↑(BitcoinSubsidy.coreSubsidy (ChainState.nextHeight ⟨H, v⟩))
        · rw [if_pos c, if_pos c]; left; exact ⟨rfl, rfl⟩
        · rw [if_neg c, if_neg c]; right; exact ⟨_, _, _, rfl, by rw [hu], he⟩

def retarget (H : List Header) (U : Ledger) : Outcome → Outcome
  | .accept _ u => .accept ⟨H, U⟩ u
  | o => o

theorem acceptHeader_retarget (H : List Header) (U U' : Ledger) (hd : Header) (nw : Int) :
    acceptHeader ⟨H, U⟩ hd nw = retarget H U (acceptHeader ⟨H, U'⟩ hd nw) := by
  have t1 : ChainState.tipHash ⟨H, U⟩ = ChainState.tipHash ⟨H, U'⟩ := by
    simp only [ChainState.tipHash, ChainState.tip]
  have t2 : ChainState.requiredBits ⟨H, U⟩ = ChainState.requiredBits ⟨H, U'⟩ := by
    simp only [ChainState.requiredBits, ChainState.tip, ChainState.tipHeight]
  have t3 : ChainState.mtp ⟨H, U⟩ = ChainState.mtp ⟨H, U'⟩ := by
    simp only [ChainState.mtp, ChainState.mtpAt, ChainState.tipHeight, ChainState.timesTo]
  have t4 : ChainState.tipHeight ⟨H, U⟩ = ChainState.tipHeight ⟨H, U'⟩ := by
    simp only [ChainState.tipHeight]
  unfold acceptHeader
  simp only [t1, t2, t3, t4]
  repeat' (first | rfl | split)

theorem contextualCheckBlock_eq (H : List Header) (U U' : Ledger) (b : Block) :
    contextualCheckBlock ⟨H, U⟩ b = contextualCheckBlock ⟨H, U'⟩ b := by
  have t3 : ChainState.mtp ⟨H, U⟩ = ChainState.mtp ⟨H, U'⟩ := by
    simp only [ChainState.mtp, ChainState.mtpAt, ChainState.tipHeight, ChainState.timesTo]
  have t4 : ChainState.tipHeight ⟨H, U⟩ = ChainState.tipHeight ⟨H, U'⟩ := by
    simp only [ChainState.tipHeight]
  have t5 : ChainState.nextHeight ⟨H, U⟩ = ChainState.nextHeight ⟨H, U'⟩ := by
    simp only [ChainState.nextHeight]
  simp only [contextualCheckBlock, t3, t4, t5]

def ORel (P Q : Outcome) : Prop :=
  (P = .invalid ∧ Q = .invalid) ∨
  (P = .futureTime ∧ Q = .futureTime) ∨
  (P = .missingPrev ∧ Q = .missingPrev) ∨
  (∃ S' T' undo, P = .accept S' undo ∧ Q = .accept T' undo ∧ StateEquiv S' T')

theorem ORel_invalid : ORel .invalid .invalid := Or.inl ⟨rfl, rfl⟩

def vrest (S : ChainState) (b : Block) : Outcome :=
  if !checkBlock b then .invalid
  else if !contextualCheckBlock S b then .invalid
  else match connectBlock S b with
    | none => .invalid
    | some (u, undo) => .accept ⟨S.headers ++ [b.header], u⟩ undo

theorem validate_eq (S : ChainState) (b : Block) (now : Int) :
    validate S b now = (match acceptHeader S b.header now with
      | .accept _ _ => vrest S b
      | o => o) := rfl

theorem vrest_equiv (H : List Header) (u v : Ledger) (hu : Equiv u v) (b : Block) :
    ORel (vrest ⟨H, u⟩ b) (vrest ⟨H, v⟩ b) := by
  unfold vrest
  rw [contextualCheckBlock_eq H u [] b, contextualCheckBlock_eq H v [] b]
  by_cases c1 : (!checkBlock b) = true
  · rw [if_pos c1, if_pos c1]; exact ORel_invalid
  · rw [if_neg c1, if_neg c1]
    by_cases c2 : (!contextualCheckBlock ⟨H, []⟩ b) = true
    · rw [if_pos c2, if_pos c2]; exact ORel_invalid
    · rw [if_neg c2, if_neg c2]
      rcases connectBlock_equiv' H u v hu b with ⟨h1, h2⟩ | ⟨u', v', undo, h1, h2, he⟩
      · rw [h1, h2]; exact ORel_invalid
      · rw [h1, h2]
        exact Or.inr (Or.inr (Or.inr ⟨_, _, undo, rfl, rfl, ⟨rfl, he⟩⟩))

theorem validate_equiv' (S T : ChainState) (h : StateEquiv S T) (b : Block) (now : Int) :
    ORel (validate S b now) (validate T b now) := by
  obtain ⟨S1, S2⟩ := S
  obtain ⟨T1, T2⟩ := T
  obtain ⟨hh, hu⟩ := h
  simp only [] at hh hu
  subst hh
  rw [validate_eq, validate_eq, acceptHeader_retarget S1 S2 [], acceptHeader_retarget S1 T2 []]
  generalize acceptHeader ⟨S1, []⟩ b.header now = A
  cases A with
  | invalid => exact ORel_invalid
  | futureTime => exact Or.inr (Or.inl ⟨rfl, rfl⟩)
  | missingPrev => exact Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))
  | accept X Y => exact vrest_equiv S1 S2 T2 hu b

theorem connectChain_equiv' (bs : List (Block × Int)) :
    ∀ (S T : ChainState), StateEquiv S T →
    (connectChain S bs = none ∧ connectChain T bs = none) ∨
    (∃ U V undos, connectChain S bs = some (U, undos) ∧ connectChain T bs = some (V, undos) ∧
      StateEquiv U V) := by
  induction bs with
  | nil =>
    intro S T h
    right; exact ⟨S, T, [], rfl, rfl, h⟩
  | cons p rest ih =>
    obtain ⟨b, now⟩ := p
    intro S T h
    rcases validate_equiv' S T h b now with ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨S', T', undo, h1, h2, he⟩
    · left; simp only [connectChain, h1, h2]; exact ⟨trivial, trivial⟩
    · left; simp only [connectChain, h1, h2]; exact ⟨trivial, trivial⟩
    · left; simp only [connectChain, h1, h2]; exact ⟨trivial, trivial⟩
    · rcases ih S' T' he with ⟨k1, k2⟩ | ⟨U, V, undos, k1, k2, ke⟩
      · left; simp only [connectChain, h1, h2, k1, k2]; exact ⟨trivial, trivial⟩
      · right
        exact ⟨U, V, undo :: undos, by simp only [connectChain, h1, k1], by simp only [connectChain, h2, k2], ke⟩

theorem connectChain_reachable' (S : ChainState) (hR : Reachable S) (bs : List (Block × Int)) :
    ∀ (S : ChainState), Reachable S → ∀ (T : ChainState) (undos : List BlockUndo),
    connectChain S bs = some (T, undos) → Reachable T := by
  induction bs with
  | nil =>
    intro S hR T undos h
    simp only [connectChain, Option.some.injEq, Prod.mk.injEq] at h
    rw [← h.1]; exact hR
  | cons p rest ih =>
    obtain ⟨b, now⟩ := p
    intro S hR T undos h
    simp only [connectChain] at h
    generalize hv : validate S b now = o at h
    cases o with
    | accept S' undo =>
      simp only [] at h
      generalize hc : connectChain S' rest = c at h
      cases c with
      | none => simp at h
      | some q =>
        obtain ⟨T0, us⟩ := q
        simp only [hc, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1]
        exact ih S' (Reachable.step hR hv) T0 us hc
    | invalid => simp at h
    | futureTime => simp at h
    | missingPrev => simp at h

theorem consistent_connectChain' (S : ChainState) (hS : Consistent S)
    (cs : List (Block × Int)) (U : ChainState) (undos : List BlockUndo)
    (h : connectChain S cs = some (U, undos)) : Consistent U := by
  obtain ⟨S0, hR, hE⟩ := hS
  rcases connectChain_equiv' cs S S0 hE with ⟨k1, _⟩ | ⟨U1, V, us, k1, k2, ke⟩
  · rw [h] at k1; exact absurd k1 (by simp)
  · rw [h] at k1
    simp only [Option.some.injEq, Prod.mk.injEq] at k1
    obtain ⟨e1, e2⟩ := k1
    subst e1
    exact ⟨V, connectChain_reachable' S0 hR cs S0 hR V us k2, ke⟩

end BtcAux

theorem solution (S : ChainState) (hR : BitcoinBlockV2.Reachable S) :
    ∀ (bs : List (BitcoinSer.Block × Int)) (T : ChainState) (undos : List BlockUndo),
    BitcoinReorg.connectChain S bs = some (T, undos) → BitcoinBlockV2.Reachable T := fun bs T undos h => BtcAux.connectChain_reachable' S hR bs S hR T undos h
