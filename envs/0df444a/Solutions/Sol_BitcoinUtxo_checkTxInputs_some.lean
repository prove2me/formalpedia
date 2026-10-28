-- Prove2me | solution 1 for BitcoinUtxo.checkTxInputs_some
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:05.171043+00:00
-- url     : https://prove2.me/submissions/908561c0-e2aa-4f18-8fe0-780f1d014cd0

import Definitions.Def_BitcoinUtxo

open BitcoinUtxo

private theorem inputsLoop_some {T : Type} [DecidableEq T] (u : UtxoSet T) (h : Nat) :
    ∀ (ops : List (OutPoint T)) (acc v : Int), inputsLoop u h ops acc = some v →
      v = acc + valueIn u ops ∧ ∀ op ∈ ops, haveCoin u op = true
  | [], acc, v, hv => by
    simp only [inputsLoop, Option.some.injEq] at hv
    subst hv; simp [valueIn]
  | op :: rest, acc, v, hv => by
    unfold inputsLoop at hv
    cases hc : getCoin u op with
    | none => rw [hc] at hv; simp at hv
    | some coin =>
      rw [hc] at hv
      simp only [] at hv
      split at hv
      · simp at hv
      · split at hv
        · simp at hv
        · obtain ⟨ih1, ih2⟩ := inputsLoop_some u h rest _ v hv
          refine ⟨?_, ?_⟩
          · unfold valueIn; rw [hc]; dsimp only; omega
          · intro op' hop'
            rcases List.mem_cons.1 hop' with rfl | hmem
            · unfold haveCoin; rw [hc]; rfl
            · exact ih2 op' hmem

/-- `CheckTxInputs` returns the fee `nValueIn - GetValueOut()`, in `MoneyRange`, with every input
present in the view. -/
theorem solution {T : Type} [DecidableEq T] (u : UtxoSet T) (tx : Tx T) (h : Nat) (fee : Int)
    (hfee : checkTxInputs u tx h = some fee) :
    fee = valueIn u tx.vin - valueOut tx ∧ 0 ≤ fee ∧ fee ≤ MAX_MONEY ∧
    ∀ op ∈ tx.vin, haveCoin u op = true := by
  unfold checkTxInputs at hfee
  split at hfee
  · simp at hfee
  · cases hl : inputsLoop u h tx.vin 0 with
    | none => rw [hl] at hfee; simp at hfee
    | some vIn =>
      rw [hl] at hfee
      simp only [] at hfee
      split at hfee
      · simp at hfee
      · split at hfee
        · simp at hfee
        · rename_i hlt hmr
          simp only [Option.some.injEq] at hfee
          subst hfee
          obtain ⟨hv, hall⟩ := inputsLoop_some u h tx.vin 0 vIn hl
          have hm : moneyRange (vIn - valueOut tx) = true := by
            cases hmr' : moneyRange (vIn - valueOut tx)
            · rw [hmr'] at hmr; simp at hmr
            · rfl
          unfold moneyRange at hm
          simp only [decide_eq_true_eq] at hm
          exact ⟨by omega, hm.1, hm.2, hall⟩
