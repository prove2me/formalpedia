-- Prove2me | solution 1 for BitcoinBlockV2.connectBlock_iff
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-28T15:13:24.511327+00:00
-- url     : https://prove2.me/submissions/4aa3a06c-c1ce-4b0a-8851-053be619a89c

import Definitions.Def_BitcoinBlockV2
import Definitions.Def_BitcoinSer

section S190BLK_sec68
open BitcoinBIP68

theorem S190BLK_delay (s : BitVec 32) : coreDelay s = specDelay s := by
  unfold coreDelay specDelay
  rw [BitVec.toNat_and]
  have : (0x0000ffff : BitVec 32).toNat = 2^16 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod]

theorem S190BLK_and_pow (x i : Nat) : x &&& 2 ^ i = 2 ^ i * (x / 2 ^ i % 2) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [Nat.testBit_and, Nat.testBit_two_pow]
  have h := Nat.mod_two_eq_zero_or_one (x / 2 ^ i)
  rcases h with h | h
  · rw [h, Nat.mul_zero, Nat.zero_testBit]
    by_cases hij : i = j
    · subst hij; simp [Nat.testBit_eq_decide_div_mod_eq, h]
    · simp [hij]
  · rw [h, Nat.mul_one, Nat.testBit_two_pow]
    by_cases hij : i = j
    · subst hij; simp [Nat.testBit_eq_decide_div_mod_eq, h]
    · simp [hij]

theorem S190BLK_bit (s : BitVec 32) (i : Nat) (hi : i < 32) :
    ((s &&& BitVec.ofNat 32 (2 ^ i)) != 0) = true ↔ s.toNat / 2 ^ i % 2 = 1 := by
  have e : (BitVec.ofNat 32 (2 ^ i)).toNat = 2 ^ i := by
    rw [BitVec.toNat_ofNat]; apply Nat.mod_eq_of_lt; exact Nat.pow_lt_pow_right (by decide) hi
  rw [bne_iff_ne, ne_eq, ← BitVec.toNat_inj, BitVec.toNat_and, e, S190BLK_and_pow, show BitVec.toNat (0 : BitVec 32) = 0 from rfl]
  have h := Nat.mod_two_eq_zero_or_one (s.toNat / 2 ^ i)
  have hp : 0 < 2 ^ i := Nat.two_pow_pos i
  rcases h with h | h <;> simp [h] <;> omega

theorem S190BLK_dis (s : BitVec 32) : coreDisabled s = true ↔ specDisabled s := by
  unfold coreDisabled specDisabled
  have := S190BLK_bit s 31 (by decide)
  have hl := s.isLt
  have : s.toNat / 2^31 < 2 := by omega
  rw [show (0x80000000 : BitVec 32) = BitVec.ofNat 32 (2^31) by decide, S190BLK_bit s 31 (by decide)]
  omega

theorem S190BLK_tb (s : BitVec 32) : coreTimeBased s = true ↔ specTimeBased s := by
  unfold coreTimeBased specTimeBased
  rw [show (0x00400000 : BitVec 32) = BitVec.ofNat 32 (2^22) by decide, S190BLK_bit s 22 (by decide)]

theorem S190BLK_sec (s : BitVec 32) : coreSeconds s = 512 * specDelay s := by
  unfold coreSeconds specDelay
  rw [BitVec.toNat_shiftLeft, BitVec.toNat_and]
  have : (0x0000ffff : BitVec 32).toNat = 2^16 - 1 := by decide
  rw [this, Nat.and_two_pow_sub_one_eq_mod, Nat.shiftLeft_eq]
  have := Nat.mod_lt s.toNat (show 0 < 2^16 by decide)
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

theorem S190BLK_en (v f : BitVec 32) : coreEnabled v f = true ↔ specEnabled v f := by
  unfold coreEnabled specEnabled
  rw [show (1 : BitVec 32) = BitVec.ofNat 32 (2^0) by decide]
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  rw [S190BLK_bit f 0 (by decide)]
  simp

def S190BLK_P (ctx : Context) (acc : Accumulator) : Prop :=
  acc.minHeight < (ctx.height : Int) ∧ acc.minTime < (ctx.mtp (ctx.height - 1) : Int)

theorem S190BLK_step (ctx : Context) (acc : Accumulator) (i : Input) :
    S190BLK_P ctx (coreStep ctx acc i) ↔ S190BLK_P ctx acc ∧ inputSatisfied ctx i := by
  unfold coreStep inputSatisfied S190BLK_P
  by_cases hd : coreDisabled i.sequence = true
  · have : specDisabled i.sequence := (S190BLK_dis _).mp hd
    simp [hd, this]
  · have hd' : ¬ specDisabled i.sequence := fun h => hd ((S190BLK_dis _).mpr h)
    by_cases ht : coreTimeBased i.sequence = true
    · have ht' : specTimeBased i.sequence := (S190BLK_tb _).mp ht
      simp only [hd, ht, if_true, Bool.false_eq_true, if_false, hd', ht', false_or, S190BLK_sec]
      simp only [Int.max_lt]
      omega
    · have ht' : ¬ specTimeBased i.sequence := fun h => ht ((S190BLK_tb _).mpr h)
      simp only [hd, ht, Bool.false_eq_true, if_false, hd', ht', false_or, S190BLK_delay]
      simp only [Int.max_lt]
      omega

theorem S190BLK_fold (ctx : Context) (l : List Input) (acc : Accumulator) :
    S190BLK_P ctx (l.foldl (coreStep ctx) acc) ↔ S190BLK_P ctx acc ∧ ∀ i ∈ l, inputSatisfied ctx i := by
  induction l generalizing acc with
  | nil => simp
  | cons i rest ih =>
    rw [List.foldl_cons, ih, S190BLK_step]
    simp only [List.mem_cons, forall_eq_or_imp]
    constructor
    · rintro ⟨⟨a, b⟩, c⟩; exact ⟨a, b, c⟩
    · rintro ⟨a, b, c⟩; exact ⟨⟨a, b⟩, c⟩

theorem S190BLK_seq (version flags : BitVec 32) (ctx : Context) (inputs : List Input) :
    sequenceLocks version flags ctx inputs = true ↔ satisfiesBIP68 version flags ctx inputs := by
  unfold sequenceLocks calculate satisfiesBIP68
  have hinit : S190BLK_P ctx initial := by
    unfold S190BLK_P initial; constructor <;> simp <;> omega
  by_cases he : coreEnabled version flags = true
  · have he' : specEnabled version flags := (S190BLK_en _ _).mp he
    rw [if_pos he]
    have := S190BLK_fold ctx inputs initial
    unfold S190BLK_P at this hinit
    simp only [evaluate, decide_eq_true_eq, he', not_true_eq_false, false_or]
    rw [this]; simp [hinit]
  · have he' : ¬ specEnabled version flags := fun h => he ((S190BLK_en _ _).mpr h)
    rw [if_neg he]
    unfold S190BLK_P initial at hinit
    simp only [evaluate, decide_eq_true_eq, he', not_false_eq_true, true_or, iff_true]
    exact hinit

end S190BLK_sec68

open BitcoinBlockV2 in
def S190BLK_InOk (u : Ledger) (H : Nat) (i : BitcoinSer.TxIn) : Prop :=
  ∃ c, getCoin u i.prevout = some c ∧
    (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY

open BitcoinBlockV2 in
theorem S190BLK_vin_nonneg (u : Ledger) (H : Nat) (l : List BitcoinSer.TxIn)
    (h : ∀ i ∈ l, S190BLK_InOk u H i) : 0 ≤ valueIn u l := by
  induction l with
  | nil => simp [valueIn]
  | cons i rest ih =>
    simp only [valueIn]
    obtain ⟨c, hc, -, h0, -⟩ := h i (by simp)
    have := ih (fun x hx => h x (by simp [hx]))
    simp only [accessCoin, hc, Option.getD_some]
    omega

open BitcoinBlockV2 in
theorem S190BLK_il (u : Ledger) (H : Nat) (l : List BitcoinSer.TxIn) (acc : Int)
    (h0 : 0 ≤ acc) (h1 : acc ≤ MAX_MONEY) :
    ((inputsLoop u H l acc).isSome = true ↔
      (∀ i ∈ l, S190BLK_InOk u H i) ∧ acc + valueIn u l ≤ MAX_MONEY) ∧
    (∀ r, inputsLoop u H l acc = some r → r = acc + valueIn u l) := by
  induction l generalizing acc with
  | nil => simp [inputsLoop, valueIn, h1]
  | cons i rest ih =>
    simp only [inputsLoop, valueIn, List.mem_cons, forall_eq_or_imp]
    cases hg : getCoin u i.prevout with
    | none =>
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq, false_implies,
        implies_true, and_true]
      rintro ⟨⟨⟨c, hc, -⟩, -⟩, -⟩
      rw [hg] at hc; cases hc
    | some c =>
      simp only [accessCoin, hg, Option.getD_some]
      by_cases hm : (c.isCoinbase && decide (H - c.height < COINBASE_MATURITY)) = true
      · simp only [hm, if_true, Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq,
          false_implies, implies_true, and_true]
        rintro ⟨⟨⟨c', hc', hmat, -⟩, -⟩, -⟩
        rw [hg] at hc'; cases hc'
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
        have := hmat hm.1
        unfold COINBASE_MATURITY at *
        omega
      · have hmat : c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H := by
          intro hc
          simp only [hc, Bool.true_and, decide_eq_true_eq] at hm
          unfold COINBASE_MATURITY at *
          omega
        simp only [hm, Bool.false_eq_true, if_false]
        by_cases hr : (!moneyRange c.out.nValue || !moneyRange (acc + c.out.nValue)) = true
        · simp only [hr, if_true, Option.isSome_none, Bool.false_eq_true, false_iff, reduceCtorEq,
            false_implies, implies_true, and_true]
          rintro ⟨⟨⟨c', hc', -, hv0, hv1⟩, hrest⟩, hs⟩
          rw [hg] at hc'; cases hc'
          have := S190BLK_vin_nonneg u H rest hrest
          simp [moneyRange] at hr
          omega
        · simp only [hr, Bool.false_eq_true, if_false]
          simp only [Bool.or_eq_true, Bool.not_eq_true', not_or, Bool.not_eq_false, moneyRange,
            decide_eq_true_eq] at hr
          obtain ⟨⟨hv0, hv1⟩, ha0, ha1⟩ := hr
          obtain ⟨ih1, ih2⟩ := ih (acc + c.out.nValue) ha0 ha1
          refine ⟨?_, ?_⟩
          · rw [ih1]
            constructor
            · rintro ⟨hr, hs⟩; exact ⟨⟨⟨c, hg, hmat, hv0, hv1⟩, hr⟩, by omega⟩
            · rintro ⟨⟨_, hr⟩, hs⟩; exact ⟨hr, by omega⟩
          · intro r hr; rw [ih2 r hr]; omega

open BitcoinBlockV2 in
theorem S190BLK_cti (u : Ledger) (tx : BitcoinSer.Tx) (H : Nat) :
    ((∃ fee, BitcoinBlockV2.checkTxInputs u tx H = some fee) ↔
      (∀ i ∈ tx.vin, ∃ c, BitcoinBlockV2.getCoin u i.prevout = some c ∧
        (c.isCoinbase = true → c.height + COINBASE_MATURITY ≤ H) ∧ 0 ≤ c.out.nValue ∧ c.out.nValue ≤ MAX_MONEY) ∧
      BitcoinBlockV2.valueIn u tx.vin ≤ MAX_MONEY ∧ BitcoinBlockV2.valueOut tx ≤ BitcoinBlockV2.valueIn u tx.vin ∧
      BitcoinBlockV2.valueIn u tx.vin - BitcoinBlockV2.valueOut tx ≤ MAX_MONEY) ∧
    (∀ fee, BitcoinBlockV2.checkTxInputs u tx H = some fee → fee = BitcoinBlockV2.feeOf u tx) := by
  obtain ⟨hl1, hl2⟩ := S190BLK_il u H tx.vin 0 (by decide) (by decide)
  simp only [Int.zero_add] at hl1 hl2
  have hall : (tx.vin.all fun i => haveCoin u i.prevout) = true ↔ ∀ i ∈ tx.vin, ∃ c, getCoin u i.prevout = some c := by
    simp [haveCoin, Option.isSome_iff_exists]
  unfold checkTxInputs feeOf
  by_cases ha : (tx.vin.all fun i => haveCoin u i.prevout) = true
  · simp only [ha, Bool.not_true, Bool.false_eq_true, if_false]
    cases hi : inputsLoop u H tx.vin 0 with
    | none =>
      rw [hi] at hl1
      simp only [Option.isSome_none, Bool.false_eq_true, false_iff] at hl1
      simp only [reduceCtorEq, exists_false, false_iff, false_implies, implies_true, and_true]
      rintro ⟨hh, h2, -⟩
      exact hl1 ⟨hh, h2⟩
    | some vi =>
      rw [hi] at hl1
      have hv := hl2 vi hi
      subst hv
      simp only [Option.isSome_some, true_iff] at hl1
      obtain ⟨hok, hle⟩ := hl1
      have hnn := S190BLK_vin_nonneg u H tx.vin hok
      by_cases c1 : valueIn u tx.vin < valueOut tx
      · simp only [c1, if_true, reduceCtorEq, exists_false, false_iff, false_implies, implies_true, and_true]
        rintro ⟨-, -, h3, -⟩; omega
      · by_cases c2 : moneyRange (valueIn u tx.vin - valueOut tx) = true
        · simp only [c1, c2, if_false, Bool.not_true, Bool.false_eq_true]
          simp only [moneyRange, decide_eq_true_eq] at c2
          refine ⟨⟨fun _ => ⟨hok, hle, by omega, c2.2⟩, fun _ => ⟨_, rfl⟩⟩, ?_⟩
          intro fee hf; cases hf; rfl
        · simp only [c1, c2, if_false, Bool.not_false, if_true, reduceCtorEq, exists_false, false_iff,
            false_implies, implies_true, and_true]
          simp only [moneyRange, decide_eq_true_eq] at c2
          rintro ⟨-, -, h3, h4⟩; omega
  · simp only [ha, Bool.not_false, if_true, reduceCtorEq, exists_false, false_iff, false_implies,
      implies_true, and_true]
    rintro ⟨hh, -⟩
    exact ha (hall.mpr (fun i hi => let ⟨c, hc, _⟩ := hh i hi; ⟨c, hc⟩))

open BitcoinBlockV2 in
theorem S190BLK_scripts (f : BitcoinActivation.ScriptFlags) (u : Ledger) (tx : BitcoinSer.Tx) :
    inputScriptsOk f u tx = true ↔ ∀ n, n < tx.vin.length →
    let i := tx.vin.getD n ⟨⟨[], 0⟩, [], 0, []⟩
    let coin := accessCoin u i.prevout
    BitcoinTaproot.verifyScriptFull (tx.vin.map fun j => (accessCoin u j.prevout).out)
      ⟨f, tx, n, coin.out.nValue⟩ i.scriptSig coin.out.scriptPubKey i.witness = true := by
  unfold inputScriptsOk
  simp only [List.all_eq_true, List.mem_range]

open BitcoinBlockV2 in
theorem S190BLK_loop_iff (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat)
    (txs : List BitcoinSer.Tx) (u : Ledger) (fees : Int) (sigOps : Nat) (undo : BlockUndo)
    (hpos : ∀ tx ∈ txs, 0 ≤ BitcoinBlockV2.valueOut tx) (hfees : 0 ≤ fees) :
    (∃ st, BitcoinBlockV2.connectLoop f H mtp ltf ⟨u, fees, sigOps, undo⟩ txs = some st) ↔
      BitcoinBlockV2.TxsSpec f H mtp ltf u fees sigOps txs := by
  induction txs generalizing u fees sigOps undo with
  | nil => simp [connectLoop, TxsSpec]
  | cons tx rest ih =>
    have hpos' : ∀ tx ∈ rest, 0 ≤ valueOut tx := fun t ht => hpos t (by simp [ht])
    have hvo : 0 ≤ valueOut tx := hpos tx (by simp)
    unfold connectLoop
    simp only [TxsSpec]
    by_cases hcb : isCoinBase tx = true
    · simp only [hcb, if_true, Bool.not_true, Bool.false_and, Bool.false_eq_true, if_false,
        reduceCtorEq, false_implies, true_and]
      by_cases hs : MAX_BLOCK_SIGOPS_COST < sigOps + txSigOpCost f u tx
      · simp only [hs, if_true, reduceCtorEq, exists_false, false_iff, not_and]
        intro h; omega
      · simp only [hs, if_false]
        rw [ih _ _ _ _ hpos' hfees]
        constructor
        · intro h; exact ⟨by omega, h⟩
        · intro h; exact h.2
    · have hcb' : isCoinBase tx = false := by simpa using hcb
      simp only [hcb', Bool.false_eq_true, if_false, Bool.not_false, Bool.true_and, true_implies]
      obtain ⟨hc1, hc2⟩ := S190BLK_cti u tx H
      cases hc : checkTxInputs u tx H with
      | none =>
        simp only [reduceCtorEq, exists_false, false_iff, not_and]
        intro hspec
        exfalso
        obtain ⟨hin, hvi, hvo2, -⟩ := hspec.1
        obtain ⟨fee, hf⟩ := hc1.mpr ⟨hin, hvi, hvo2, by omega⟩
        rw [hc] at hf; cases hf
      | some fee =>
        have hfe : fee = feeOf u tx := hc2 fee hc
        subst hfe
        obtain ⟨hin, hvi, hvo2, -⟩ := hc1.mp ⟨_, hc⟩
        have hfnn : 0 ≤ feeOf u tx := by unfold feeOf; omega
        simp only
        by_cases hm : moneyRange (fees + feeOf u tx) = true
        · have hm' : fees + feeOf u tx ≤ MAX_MONEY := by simp [moneyRange] at hm; omega
          simp only [hm, Bool.not_true, Bool.false_eq_true, if_false]
          by_cases hq : sequenceLocksOk u H mtp ltf tx = true
          · have hq' := (S190BLK_seq _ _ _ _).mp hq
            simp only [hq, Bool.not_true, Bool.false_eq_true, if_false]
            by_cases hs : MAX_BLOCK_SIGOPS_COST < sigOps + txSigOpCost f u tx
            · simp only [hs, if_true, reduceCtorEq, exists_false, false_iff, not_and]
              intro _ h; omega
            · simp only [hs, if_false]
              by_cases hsc : inputScriptsOk f u tx = true
              · simp only [hsc, Bool.not_true, Bool.false_eq_true, if_false]
                rw [ih _ _ _ _ hpos' (by omega)]
                have hsc' := (S190BLK_scripts f u tx).mp hsc
                constructor
                · intro h
                  exact ⟨⟨⟨hin, hvi, hvo2, hq', hsc'⟩, hm'⟩, by omega, h⟩
                · intro h; exact h.2.2
              · simp only [hsc, Bool.not_false, if_true, reduceCtorEq, exists_false, false_iff, not_and]
                intro h
                exact absurd ((S190BLK_scripts f u tx).mpr h.1.2.2.2.2) hsc
          · simp only [hq, Bool.not_false, if_true, reduceCtorEq, exists_false, false_iff, not_and]
            intro h
            exact absurd ((S190BLK_seq _ _ _ _).mpr h.1.2.2.2.1) hq
        · simp only [hm, Bool.not_false, if_true, reduceCtorEq, exists_false, false_iff, not_and]
          intro h
          exfalso; apply hm
          have h2 := h.2
          simp only [moneyRange, decide_eq_true_eq]
          exact ⟨by omega, h2⟩


open BitcoinBlockV2 in
theorem S190BLK_loop_fees (f : BitcoinActivation.ScriptFlags) (H : Nat) (mtp : Nat → Nat) (ltf : Nat)
    (txs : List BitcoinSer.Tx) (st st' : LoopState) (h : connectLoop f H mtp ltf st txs = some st') :
    st'.fees = st.fees + totalFees H st.utxo txs := by
  induction txs generalizing st with
  | nil => simp [connectLoop] at h; subst h; simp [totalFees]
  | cons tx rest ih =>
    unfold connectLoop at h
    simp only at h
    by_cases hcb : isCoinBase tx = true
    · simp only [hcb, if_true] at h
      split at h
      · cases h
      · split at h
        · cases h
        · have := ih _ h
          simp only at this
          rw [this]; simp [totalFees, hcb]
    · have hcb' : isCoinBase tx = false := by simpa using hcb
      simp only [hcb', Bool.false_eq_true, if_false] at h
      cases hc : checkTxInputs st.utxo tx H with
      | none => simp [hc] at h
      | some fee =>
        have hfe := ((S190BLK_cti st.utxo tx H).2 fee hc)
        simp only [hc] at h
        by_cases hm : moneyRange (st.fees + fee) = true
        · by_cases hq : sequenceLocksOk st.utxo H mtp ltf tx = true
          · simp only [hm, hq, Bool.not_true, Bool.false_eq_true, if_false] at h
            split at h
            · cases h
            · split at h
              · cases h
              · have := ih _ h
                simp only at this
                rw [this, hfe]; simp [totalFees, hcb']; omega
          · simp [hm, hq] at h
        · simp [hm] at h

theorem S190BLK_subsidy (h : Nat) : BitcoinSubsidy.coreSubsidy h = BitcoinSubsidy.specSubsidy h := by
  unfold BitcoinSubsidy.coreSubsidy BitcoinSubsidy.specSubsidy
  simp only
  split
  · rename_i hh
    symm
    apply Nat.div_eq_of_lt
    have : 2 ^ 64 ≤ 2 ^ (h / BitcoinSubsidy.halvingInterval) := Nat.pow_le_pow_right (by decide) hh
    have : 50 * BitcoinSubsidy.COIN < 2 ^ 64 := by decide
    omega
  · rw [Nat.shiftRight_eq_div_pow]

open BitcoinBlockV2 in
theorem S190BLK_bip30Ok (u : Ledger) (b : BitcoinSer.Block) :
    bip30Ok u b = true ↔ ∀ tx ∈ b.vtx, ∀ o, o < tx.vout.length → getCoin u ⟨BitcoinSer.txid tx, o⟩ = none := by
  unfold bip30Ok haveCoin
  simp [List.all_eq_true, List.mem_range]

open BitcoinBlockV2 in
theorem solution (S : ChainState) (b : BitcoinSer.Block) (hne : b.vtx ≠ [])
    (hpos : ∀ tx ∈ b.vtx, 0 ≤ BitcoinBlockV2.valueOut tx) :
    (∃ r, BitcoinBlockV2.connectBlock S b = some r) ↔ BitcoinBlockV2.LedgerSpec S b := by
  unfold connectBlock LedgerSpec
  by_cases hg : BitcoinSer.headerHash b.header = BitcoinSer.genesisHash
  · simp [hg]
  · simp only [hg, if_false, false_or]
    have hl := S190BLK_loop_iff (BitcoinActivation.blockScriptFlags S.nextHeight (scriptException (BitcoinSer.headerHash b.header)))
      S.nextHeight S.mtpNat (BitcoinActivation.lockTimeFlags S.nextHeight) b.vtx S.utxo 0 0 [] hpos (by decide)
    obtain ⟨cb, rest, hv⟩ : ∃ cb rest, b.vtx = cb :: rest := by
      cases h : b.vtx with
      | nil => exact absurd h hne
      | cons cb rest => exact ⟨cb, rest, rfl⟩
    by_cases h30 : (bip30Checked S S.nextHeight (BitcoinSer.headerHash b.header) && !bip30Ok S.utxo b) = true
    · simp only [h30, if_true, reduceCtorEq, exists_false, false_iff, not_and]
      intro h
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at h30
      exact absurd ((S190BLK_bip30Ok _ _).mpr (h h30.1)) (by simp [h30.2])
    · simp only [h30, Bool.false_eq_true, if_false]
      have hb : bip30Checked S S.nextHeight (BitcoinSer.headerHash b.header) = true →
          ∀ tx ∈ b.vtx, ∀ o, o < tx.vout.length → getCoin S.utxo ⟨BitcoinSer.txid tx, o⟩ = none := by
        intro hc
        apply (S190BLK_bip30Ok _ _).mp
        simp only [hc, Bool.true_and, Bool.not_eq_true'] at h30
        simpa using h30
      cases hlp : connectLoop (BitcoinActivation.blockScriptFlags S.nextHeight (scriptException (BitcoinSer.headerHash b.header)))
          S.nextHeight S.mtpNat (BitcoinActivation.lockTimeFlags S.nextHeight) ⟨S.utxo, 0, 0, []⟩ b.vtx with
      | none =>
        rw [hlp] at hl
        simp only [reduceCtorEq, exists_false, false_iff] at hl
        simp only [reduceCtorEq, exists_false, false_iff, not_and]
        intro _ h; exact absurd h hl
      | some st =>
        rw [hlp] at hl
        have hts : TxsSpec (BitcoinActivation.blockScriptFlags S.nextHeight (scriptException (BitcoinSer.headerHash b.header)))
            S.nextHeight S.mtpNat (BitcoinActivation.lockTimeFlags S.nextHeight) S.utxo 0 0 b.vtx := hl.mp ⟨_, rfl⟩
        have hf := S190BLK_loop_fees _ _ _ _ _ _ _ hlp
        simp only [Int.zero_add] at hf
        simp only
        rw [hv] at hf ⊢
        rw [hv] at hb hts
        simp only [List.headD_cons, List.take_succ_cons, List.take_zero, List.mem_singleton, forall_eq,
          S190BLK_subsidy, hf]
        by_cases hc : valueOut cb > totalFees S.nextHeight S.utxo (cb :: rest) + (BitcoinSubsidy.specSubsidy S.nextHeight : Int)
        · simp only [hc, if_true, reduceCtorEq, exists_false, false_iff, not_and]
          intro _ _ h; omega
        · simp only [hc, if_false]
          constructor
          · intro _; exact ⟨hb, hts, by omega⟩
          · intro _; exact ⟨_, rfl⟩
