-- Prove2me | solution 1 for BitcoinUtxo.checkTransaction_outputs
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:04.480995+00:00
-- url     : https://prove2.me/submissions/a5d261d6-a381-4ca1-9af1-4fe870521b90

import Definitions.Def_BitcoinUtxo

open BitcoinUtxo

private theorem outputsLoop_some :
    ∀ (outs : List TxOut) (acc v : Int), outputsLoop outs acc = some v →
      v = acc + sumValues outs ∧ ∀ o ∈ outs, 0 ≤ o.value ∧ o.value ≤ MAX_MONEY
  | [], acc, v, hv => by
    simp only [outputsLoop, Option.some.injEq] at hv
    subst hv; simp [sumValues]
  | o :: rest, acc, v, hv => by
    unfold outputsLoop at hv
    split at hv
    · simp at hv
    · split at hv
      · simp at hv
      · split at hv
        · simp at hv
        · obtain ⟨ih1, ih2⟩ := outputsLoop_some rest _ v hv
          refine ⟨by unfold sumValues; omega, ?_⟩
          intro o' ho'
          rcases List.mem_cons.1 ho' with rfl | hmem
          · constructor <;> omega
          · exact ih2 o' hmem

theorem solution {T : Type} [DecidableEq T] (tx : Tx T) (h : checkTransaction tx = true) :
    tx.vin.Nodup ∧ ∀ o ∈ tx.vout, 0 ≤ o.value ∧ o.value ≤ MAX_MONEY := by
  unfold checkTransaction at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨-, -⟩, hsome⟩, hnd⟩ := h
  refine ⟨hnd, ?_⟩
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.1 hsome
  exact (outputsLoop_some tx.vout 0 v hv).2
