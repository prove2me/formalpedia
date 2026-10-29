-- Prove2me | solution 1 for BitcoinReorg.disconnectChain_connectChain
-- status  : ACCEPTED   (prove)
-- author  : @Ethan Cheung Wang
-- created : 2026-10-29T02:45:42.238977+00:00
-- url     : https://prove2.me/submissions/7392d515-cca7-4b5e-956d-55f7f8b1160c

import Theorems.Thm_BitcoinBlockV2_disconnect_connect
import Theorems.Thm_BitcoinBlockV2_reachable_wellFormed
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

open BitcoinReorg BitcoinBlockV2

namespace BtcAux
open BitcoinSer

def PosC (u : Ledger) : Prop := ∀ e ∈ u, 1 ≤ e.2.height
def UndoPos (undo : BlockUndo) : Prop := ∀ cs ∈ undo, ∀ c ∈ cs, 1 ≤ c.height

theorem mem_spendCoin (u : Ledger) (op : OutPoint) : ∀ e, e ∈ spendCoin u op → e ∈ u := by
  induction u with
  | nil => intro e h; simp only [spendCoin] at h; exact h
  | cons p rest ih =>
    intro e h
    obtain ⟨k, c⟩ := p
    by_cases hk : k = op
    · simp only [spendCoin, hk, if_true] at h
      exact List.mem_cons_of_mem _ (ih e h)
    · simp only [spendCoin, hk, if_false] at h
      cases h with
      | head => exact List.mem_cons_self
      | tail _ h => exact List.mem_cons_of_mem _ (ih e h)

theorem posC_spendCoin {u : Ledger} (h : PosC u) (op : OutPoint) : PosC (spendCoin u op) :=
  fun e he => h e (mem_spendCoin u op e he)

theorem posC_addCoin {u : Ledger} (h : PosC u) (op : OutPoint) (c : Coin) (hc : 1 ≤ c.height) :
    PosC (addCoin u op c) := by
  unfold addCoin
  by_cases hu : isUnspendable c.out.scriptPubKey = true
  · rw [if_pos hu]; exact h
  · rw [if_neg hu]
    intro e he
    cases he with
    | head => exact hc
    | tail _ he => exact h e (mem_spendCoin u op e he)

theorem posC_addCoinsFrom (txid : Bytes) (height : Nat) (cb : Bool) (hh : 1 ≤ height) (outs : List TxOut) :
    ∀ (u : Ledger) (i : Nat), PosC u → PosC (addCoinsFrom txid height cb u i outs) := by
  induction outs with
  | nil => intro u i h; exact h
  | cons o rest ih =>
    intro u i h
    simp only [addCoinsFrom]
    exact ih _ _ (posC_addCoin h _ _ hh)

theorem posC_spendInputs (ins : List TxIn) : ∀ u, PosC u → PosC (spendInputs u ins) := by
  induction ins with
  | nil => intro u h; exact h
  | cons i rest ih =>
    intro u h
    simp only [spendInputs]
    exact ih _ (posC_spendCoin h _)

theorem posC_updateCoins {u : Ledger} (h : PosC u) (tx : Tx) (H : Nat) (hH : 1 ≤ H) :
    PosC (updateCoins u tx H) := by
  unfold updateCoins
  apply posC_addCoinsFrom _ _ _ hH
  by_cases hc : isCoinBase tx = true
  · rw [if_pos hc]; exact h
  · rw [if_neg hc]; exact posC_spendInputs _ _ h

theorem getCoin_mem (u : Ledger) (op : OutPoint) (c : Coin) : getCoin u op = some c → ∃ k, (k, c) ∈ u := by
  induction u with
  | nil => intro h; simp only [getCoin] at h; cases h
  | cons p rest ih =>
    obtain ⟨k, c'⟩ := p
    intro h
    by_cases hk : k = op
    · simp only [getCoin, hk, if_true] at h
      cases h
      exact ⟨k, List.mem_cons_self⟩
    · simp only [getCoin, hk, if_false] at h
      obtain ⟨k', hk'⟩ := ih h
      exact ⟨k', List.mem_cons_of_mem _ hk'⟩

theorem checkTxInputs_have (u : Ledger) (tx : Tx) (h : Nat) (fee : Int)
    (hc : checkTxInputs u tx h = some fee) : tx.vin.all (fun i => haveCoin u i.prevout) = true := by
  unfold checkTxInputs at hc
  by_cases ha : tx.vin.all (fun i => haveCoin u i.prevout) = true
  · exact ha
  · have : (!(tx.vin.all fun i => haveCoin u i.prevout)) = true := by
      cases hh : tx.vin.all (fun i => haveCoin u i.prevout)
      · rfl
      · exact absurd hh ha
    rw [if_pos this] at hc
    cases hc

theorem txUndo_pos {u : Ledger} (hp : PosC u) (tx : Tx)
    (ha : tx.vin.all (fun i => haveCoin u i.prevout) = true) : ∀ c ∈ txUndo u tx, 1 ≤ c.height := by
  intro c hc
  unfold txUndo at hc
  rw [List.mem_map] at hc
  obtain ⟨i, hi, rfl⟩ := hc
  have h1 : haveCoin u i.prevout = true := List.all_eq_true.mp ha i hi
  unfold haveCoin at h1
  cases hg : getCoin u i.prevout with
  | none => rw [hg] at h1; exact Bool.noConfusion h1
  | some c' =>
    obtain ⟨k, hk⟩ := getCoin_mem u _ c' hg
    unfold accessCoin
    rw [hg]
    exact hp (k, c') hk

end BtcAux

open BitcoinReorg BitcoinBlockV2

namespace BtcAux
open BitcoinSer

theorem connectLoop_pos (f : BitcoinActivation.ScriptFlags) (height : Nat) (mtp : Nat → Nat) (lf : Nat)
    (hh : 1 ≤ height) (txs : List Tx) :
    ∀ (st : LoopState), PosC st.utxo → UndoPos st.undo →
      ∀ st', connectLoop f height mtp lf st txs = some st' → PosC st'.utxo ∧ UndoPos st'.undo := by
  induction txs with
  | nil =>
    intro st hp hu st' h
    simp only [connectLoop] at h
    cases h
    exact ⟨hp, hu⟩
  | cons tx rest ih =>
    intro st hp hu st' h
    obtain ⟨u, fees, sigOps, undo⟩ := st
    simp only [] at hp hu
    simp only [connectLoop] at h
    by_cases hc : isCoinBase tx = true
    · rw [if_pos hc] at h
      simp only [] at h
      by_cases c1 : MAX_BLOCK_SIGOPS_COST < sigOps + txSigOpCost f u tx
      · rw [if_pos c1] at h; cases h
      · rw [if_neg c1] at h
        by_cases c2 : (!isCoinBase tx && !inputScriptsOk f u tx) = true
        · rw [if_pos c2] at h; cases h
        · rw [if_neg c2] at h
          exact ih _ (posC_updateCoins hp tx height hh) hu st' h
    · rw [if_neg hc] at h
      generalize hck : checkTxInputs u tx height = r at h
      cases r with
      | none => simp only [] at h; cases h
      | some fee =>
        simp only [] at h
        by_cases d1 : (!moneyRange (fees + fee)) = true
        · rw [if_pos d1] at h; cases h
        · rw [if_neg d1] at h
          by_cases d2 : (!sequenceLocksOk u height mtp lf tx) = true
          · rw [if_pos d2] at h; cases h
          · rw [if_neg d2] at h
            simp only [] at h
            by_cases c1 : MAX_BLOCK_SIGOPS_COST < sigOps + txSigOpCost f u tx
            · rw [if_pos c1] at h; cases h
            · rw [if_neg c1] at h
              by_cases c2 : (!isCoinBase tx && !inputScriptsOk f u tx) = true
              · rw [if_pos c2] at h; cases h
              · rw [if_neg c2] at h
                have hu' : UndoPos (undo ++ [txUndo u tx]) := by
                  intro cs hcs c hcc
                  rcases List.mem_append.mp hcs with h1 | h1
                  · exact hu cs h1 c hcc
                  · have : cs = txUndo u tx := List.mem_singleton.mp h1
                    subst this
                    exact txUndo_pos hp tx (checkTxInputs_have u tx height fee hck) c hcc
                exact ih _ (posC_updateCoins hp tx height hh) hu' st' h

theorem connectBlock_pos (S : ChainState) (b : Block) (hp : PosC S.utxo) (hh : 1 ≤ S.nextHeight)
    (u : Ledger) (undo : BlockUndo) (h : connectBlock S b = some (u, undo)) :
    PosC u ∧ UndoPos undo := by
  unfold connectBlock at h
  by_cases g : headerHash b.header = genesisHash
  · rw [if_pos g] at h
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    subst h1; subst h2
    exact ⟨hp, fun cs hcs => nomatch hcs⟩
  · rw [if_neg g] at h
    by_cases b1 : (bip30Checked S S.nextHeight (headerHash b.header) && !bip30Ok S.utxo b) = true
    · rw [if_pos b1] at h; cases h
    · rw [if_neg b1] at h
      dsimp only at h
      split at h
      · cases h
      · rename_i st hl
        by_cases c : valueOut (b.vtx.headD genesisCoinbase) > st.fees + ↑(BitcoinSubsidy.coreSubsidy S.nextHeight)
        · simp only [c, if_true] at h; cases h
        · simp only [c, if_false, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2
          exact connectLoop_pos _ _ _ _ hh _ ⟨S.utxo, 0, 0, []⟩ hp (fun cs hcs => nomatch hcs) st hl

end BtcAux

open BitcoinReorg BitcoinBlockV2

namespace BtcAux
open BitcoinSer

def DRel (a b : Option (Ledger × Bool)) : Prop :=
  (a = none ∧ b = none) ∨ ∃ x y c, a = some (x, c) ∧ b = some (y, c) ∧ Equiv x y

theorem spendOutputs_equiv (txid : Bytes) (height : Nat) (cb ex : Bool) (outs : List TxOut) :
    ∀ (u v : Ledger) (i : Nat), Equiv u v →
      (spendOutputs u txid height cb ex outs i).2 = (spendOutputs v txid height cb ex outs i).2 ∧
      Equiv (spendOutputs u txid height cb ex outs i).1 (spendOutputs v txid height cb ex outs i).1 := by
  induction outs with
  | nil => intro u v i h; exact ⟨rfl, h⟩
  | cons o rest ih =>
    intro u v i h
    simp only [spendOutputs]
    by_cases hu : isUnspendable o.scriptPubKey = true
    · simp only [hu, ↓reduceIte]
      have := ih u v (i + 1) h
      exact ⟨by rw [this.1], this.2⟩
    · have hu' : isUnspendable o.scriptPubKey = false := by
        cases hh : isUnspendable o.scriptPubKey
        · rfl
        · exact absurd hh hu
      simp only [hu', Bool.false_eq_true, ↓reduceIte]
      have := ih (spendCoin u ⟨txid, i⟩) (spendCoin v ⟨txid, i⟩) (i + 1) (equiv_spendCoin h _)
      rw [h ⟨txid, i⟩]
      exact ⟨by rw [this.1], this.2⟩

theorem applyTxInUndo_pos (u : Ledger) (c : Coin) (op : OutPoint) (hc : 1 ≤ c.height) :
    applyTxInUndo u c op = some (addCoin u op c, !haveCoin u op) := by
  unfold applyTxInUndo
  have : ¬ c.height = 0 := by omega
  simp only [this, if_false]

theorem restoreInputs_equiv (l : List (TxIn × Coin)) (hl : ∀ p ∈ l, 1 ≤ p.2.height) :
    ∀ (u v : Ledger), Equiv u v → DRel (restoreInputs u l) (restoreInputs v l) := by
  induction l with
  | nil => intro u v h; right; exact ⟨u, v, true, rfl, rfl, h⟩
  | cons p rest ih =>
    intro u v h
    obtain ⟨i, c⟩ := p
    have hc : 1 ≤ c.height := hl (i, c) List.mem_cons_self
    have hr := ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) u v h
    simp only [restoreInputs]
    rcases hr with ⟨h1, h2⟩ | ⟨x, y, cl, h1, h2, hxy⟩
    · rw [h1, h2]; left; exact ⟨rfl, rfl⟩
    · rw [h1, h2]
      simp only [applyTxInUndo_pos _ _ _ hc, haveCoin_eq hxy]
      right
      exact ⟨_, _, _, rfl, rfl, equiv_addCoin hxy _ _⟩

end BtcAux

open BitcoinReorg BitcoinBlockV2

namespace BtcAux
open BitcoinSer

def PosO (o : Option (List Coin)) : Prop := ∀ cs, o = some cs → ∀ c ∈ cs, 1 ≤ c.height

theorem disconnectTx_equiv (height : Nat) (ex : Bool) (tx : Tx) (undo : Option (List Coin)) (hp : PosO undo)
    (u v : Ledger) (h : Equiv u v) :
    DRel (disconnectTx u height ex tx undo) (disconnectTx v height ex tx undo) := by
  unfold disconnectTx
  dsimp only
  have hs := spendOutputs_equiv (txid tx) height (isCoinBase tx) (isCoinBase tx && ex) tx.vout u v 0 h
  generalize spendOutputs u (txid tx) height (isCoinBase tx) (isCoinBase tx && ex) tx.vout 0 = A at hs
  generalize spendOutputs v (txid tx) height (isCoinBase tx) (isCoinBase tx && ex) tx.vout 0 = B at hs
  obtain ⟨A1, A2⟩ := A
  obtain ⟨B1, B2⟩ := B
  obtain ⟨hs1, hs2⟩ := hs
  simp only [] at hs1 hs2
  subst hs1
  cases undo with
  | none => right; exact ⟨_, _, _, rfl, rfl, hs2⟩
  | some coins =>
    simp only []
    by_cases hl : coins.length ≠ tx.vin.length
    · rw [if_pos hl, if_pos hl]; left; exact ⟨rfl, rfl⟩
    · rw [if_neg hl, if_neg hl]
      have hpos : ∀ p ∈ tx.vin.zip coins, 1 ≤ p.2.height := by
        intro p hpm
        exact hp coins rfl p.2 (List.of_mem_zip hpm).2
      rcases restoreInputs_equiv _ hpos A1 B1 hs2 with ⟨h1, h2⟩ | ⟨x, y, cl, h1, h2, hxy⟩
      · rw [h1, h2]; left; exact ⟨rfl, rfl⟩
      · rw [h1, h2]; right; exact ⟨_, _, _, rfl, rfl, hxy⟩

theorem disconnectTxs_equiv (height : Nat) (ex : Bool) (l : List (Tx × Option (List Coin)))
    (hl : ∀ p ∈ l, PosO p.2) :
    ∀ (u v : Ledger), Equiv u v → DRel (disconnectTxs height ex u l) (disconnectTxs height ex v l) := by
  induction l with
  | nil => intro u v h; right; exact ⟨u, v, true, rfl, rfl, h⟩
  | cons p rest ih =>
    intro u v h
    obtain ⟨tx, undo⟩ := p
    simp only [disconnectTxs]
    rcases disconnectTx_equiv height ex tx undo (hl (tx, undo) List.mem_cons_self) u v h with
      ⟨h1, h2⟩ | ⟨x, y, c, h1, h2, hxy⟩
    · rw [h1, h2]; left; exact ⟨rfl, rfl⟩
    · rw [h1, h2]
      simp only []
      rcases ih (fun q hq => hl q (List.mem_cons_of_mem _ hq)) x y hxy with ⟨g1, g2⟩ | ⟨x', y', c', g1, g2, gxy⟩
      · rw [g1, g2]; left; exact ⟨rfl, rfl⟩
      · rw [g1, g2]; right; exact ⟨_, _, _, rfl, rfl, gxy⟩

theorem disconnectBlock_equiv (height : Nat) (hash : Bytes) (b : Block) (undo : BlockUndo) (hu : UndoPos undo)
    (u v : Ledger) (h : Equiv u v) :
    DRel (disconnectBlock u height hash b undo) (disconnectBlock v height hash b undo) := by
  unfold disconnectBlock
  by_cases hn : undo.length + 1 ≠ b.vtx.length
  · rw [if_pos hn, if_pos hn]; left; exact ⟨rfl, rfl⟩
  · rw [if_neg hn, if_neg hn]
    apply disconnectTxs_equiv _ _ _ _ u v h
    intro p hp
    rw [List.mem_reverse] at hp
    have hm := (List.of_mem_zip hp).2
    intro cs hcs c hc
    rcases List.mem_cons.mp hm with he | hm
    · rw [he] at hcs; cases hcs
    · rw [List.mem_map] at hm
      obtain ⟨cs', hcs', he⟩ := hm
      rw [← he] at hcs
      cases hcs
      exact hu _ hcs' c hc

theorem validate_cb (S : ChainState) (b : Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : validate S b now = .accept S' undo) : connectBlock S b = some (S'.utxo, undo) := by
  rw [validate_eq] at h
  generalize acceptHeader S b.header now = A at h
  cases A with
  | invalid => cases h
  | futureTime => cases h
  | missingPrev => cases h
  | accept X Y =>
    simp only [] at h
    unfold vrest at h
    by_cases c1 : (!checkBlock b) = true
    · rw [if_pos c1] at h; cases h
    · rw [if_neg c1] at h
      by_cases c2 : (!contextualCheckBlock S b) = true
      · rw [if_pos c2] at h; cases h
      · rw [if_neg c2] at h
        generalize hc : connectBlock S b = r at h
        cases r with
        | none => cases h
        | some p =>
          obtain ⟨u, un⟩ := p
          simp only [Outcome.accept.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1; subst h2
          rfl

end BtcAux

open BitcoinReorg BitcoinBlockV2

theorem BtcAux.dce (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hwf : BitcoinBlockV2.WellFormed S) (hnd : (b.vtx.map BitcoinSer.txid).Nodup)
    (hfresh : ∀ tx ∈ b.vtx, ∀ o, BitcoinBlockV2.getCoin S.utxo ⟨BitcoinSer.txid tx, o⟩ = none)
    (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash)
    (h : BitcoinBlockV2.validate S b now = .accept S' undo) (v : Ledger) (hv : BitcoinBlockV2.Equiv v S'.utxo) :
    ∃ u, BitcoinBlockV2.disconnectBlock v S.nextHeight (BitcoinSer.headerHash b.header) b undo = some (u, true) ∧
      BitcoinBlockV2.Equiv u S.utxo := by
  have hcb := BtcAux.validate_cb S b now S' undo h
  have hp : BtcAux.PosC S.utxo := fun e he => (hwf.2.2 e he).1
  have hh : 1 ≤ S.nextHeight := by
    obtain ⟨h1, _⟩ := hwf
    unfold ChainState.nextHeight
    cases hH : S.headers with
    | nil => rw [hH] at h1; cases h1
    | cons a l => simp only [List.length_cons]; omega
  have hpos := BtcAux.connectBlock_pos S b hp hh _ undo hcb
  obtain ⟨u, hu1, hu2⟩ := BitcoinBlockV2.disconnect_connect S b now S' undo hwf hnd hfresh hg h
  rcases BtcAux.disconnectBlock_equiv S.nextHeight (BitcoinSer.headerHash b.header) b undo hpos.2 v S'.utxo hv with
    ⟨a1, a2⟩ | ⟨x, y, c, a1, a2, hxy⟩
  · rw [hu1] at a2; cases a2
  · rw [hu1] at a2
    simp only [Option.some.injEq, Prod.mk.injEq] at a2
    obtain ⟨e1, e2⟩ := a2
    subst e1; subst e2
    exact ⟨x, a1, fun op => by rw [hxy op, hu2 op]⟩

open BitcoinReorg BitcoinBlockV2

namespace BtcAux
open BitcoinSer

theorem dc_append (l : List (Block × BlockUndo)) (m : List (Block × BlockUndo)) :
    ∀ (S S1 S2 : ChainState) (c1 c2 : Bool), disconnectChain S l = some (S1, c1) →
      disconnectChain S1 m = some (S2, c2) → disconnectChain S (l ++ m) = some (S2, c1 && c2) := by
  induction l with
  | nil =>
    intro S S1 S2 c1 c2 h1 h2
    simp only [disconnectChain, Option.some.injEq, Prod.mk.injEq] at h1
    obtain ⟨e1, e2⟩ := h1
    subst e1; subst e2
    simp only [List.nil_append, h2, Bool.true_and]
  | cons p rest ih =>
    intro S S1 S2 c1 c2 h1 h2
    obtain ⟨b, un⟩ := p
    simp only [disconnectChain] at h1
    simp only [List.cons_append, disconnectChain]
    cases ht : disconnectTip S b un with
    | none => rw [ht] at h1; cases h1
    | some q =>
      obtain ⟨S', cl⟩ := q
      rw [ht] at h1
      simp only [] at h1
      cases hr : disconnectChain S' rest with
      | none => rw [hr] at h1; cases h1
      | some r =>
        obtain ⟨R, cr⟩ := r
        rw [hr] at h1
        simp only [Option.some.injEq, Prod.mk.injEq] at h1
        obtain ⟨e1, e2⟩ := h1
        subst e1; subst e2
        simp only [ih S' R S2 cr c2 hr h2, Bool.and_assoc]

theorem validate_hd (S : ChainState) (b : Block) (now : Int) (S' : ChainState) (undo : BlockUndo)
    (h : validate S b now = .accept S' undo) : S'.headers = S.headers ++ [b.header] := by
  rw [validate_eq] at h
  generalize acceptHeader S b.header now = A at h
  cases A with
  | invalid => cases h
  | futureTime => cases h
  | missingPrev => cases h
  | accept X Y =>
    simp only [] at h
    unfold vrest at h
    by_cases c1 : (!checkBlock b) = true
    · rw [if_pos c1] at h; cases h
    · rw [if_neg c1] at h
      by_cases c2 : (!contextualCheckBlock S b) = true
      · rw [if_pos c2] at h; cases h
      · rw [if_neg c2] at h
        generalize hc : connectBlock S b = r at h
        cases r with
        | none => cases h
        | some p =>
          obtain ⟨u, un⟩ := p
          simp only [Outcome.accept.injEq] at h
          obtain ⟨h1, h2⟩ := h
          subst h1
          rfl

theorem dcc (bs : List (Block × Int)) :
    ∀ (S : ChainState), Reachable S → FreshChain S bs →
    ∀ (T : ChainState) (undos : List BlockUndo), connectChain S bs = some (T, undos) →
    ∃ S', disconnectChain T ((bs.map Prod.fst).zip undos).reverse = some (S', true) ∧ StateEquiv S' S := by
  induction bs with
  | nil =>
    intro S hR hF T undos h
    simp only [connectChain, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨e1, e2⟩ := h
    subst e1; subst e2
    exact ⟨S, by simp only [List.map, List.zip_nil_left, List.reverse_nil, disconnectChain], rfl, fun _ => rfl⟩
  | cons p rest ih =>
    intro S hR hF T undos h
    obtain ⟨b, now⟩ := p
    simp only [connectChain] at h
    cases hv : validate S b now with
    | invalid => rw [hv] at h; cases h
    | futureTime => rw [hv] at h; cases h
    | missingPrev => rw [hv] at h; cases h
    | accept S' un =>
      rw [hv] at h
      simp only [] at h
      cases hc : connectChain S' rest with
      | none => rw [hc] at h; cases h
      | some r =>
        obtain ⟨T0, us⟩ := r
        rw [hc] at h
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨e1, e2⟩ := h
        subst e1; subst e2
        simp only [FreshChain] at hF
        obtain ⟨hnd, hfr, hg, hF'⟩ := hF
        have hR' : Reachable S' := Reachable.step hR hv
        obtain ⟨S'', hd, hS1, hS2⟩ := ih S' hR' (hF' S' un hv) T0 us hc
        have hwf := BitcoinBlockV2.reachable_wellFormed S hR
        have hhd := validate_hd S b now S' un hv
        obtain ⟨u, hu1, hu2⟩ := dce S b now S' un hwf hnd hfr hg hv S''.utxo (fun op => (hS2 op))
        have htip : S''.tipHeight = S.nextHeight := by
          simp only [ChainState.tipHeight, ChainState.nextHeight, hS1, hhd, List.length_append, List.length_cons,
            List.length_nil]
          omega
        have hlast : disconnectChain S'' [(b, un)] = some (⟨S''.headers.dropLast, u⟩, true) := by
          simp only [disconnectChain, disconnectTip, htip, hu1, Bool.and_true]
        refine ⟨⟨S''.headers.dropLast, u⟩, ?_, ?_, ?_⟩
        · simp only [List.map, List.zip_cons_cons, List.reverse_cons]
          have := dc_append _ [(b, un)] T0 S'' _ true true hd hlast
          simpa only [Bool.and_true] using this
        · simp only [hS1, hhd, List.dropLast_concat]
        · exact hu2

end BtcAux

theorem solution (bs : List (BitcoinSer.Block × Int)) :
    ∀ (S : ChainState), BitcoinBlockV2.Reachable S → BitcoinReorg.FreshChain S bs →
    ∀ (T : ChainState) (undos : List BlockUndo), BitcoinReorg.connectChain S bs = some (T, undos) →
    ∃ S', BitcoinReorg.disconnectChain T ((bs.map Prod.fst).zip undos).reverse = some (S', true) ∧
      BitcoinReorg.StateEquiv S' S := BtcAux.dcc bs
