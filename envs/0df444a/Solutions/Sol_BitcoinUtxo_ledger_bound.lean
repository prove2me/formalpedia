-- Prove2me | solution 1 for BitcoinUtxo.ledger_bound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:10.058801+00:00
-- url     : https://prove2.me/submissions/b82d9e06-f8f8-4948-b46b-01eabf78e9a5

import Definitions.Def_BitcoinUtxo
import Theorems.Thm_BitcoinUtxo_chain_bound

open BitcoinUtxo

/-- From an empty ledger, the total value after any sequence of accepted blocks is at most the sum
of their subsidies. -/
theorem solution {T : Type} [DecidableEq T] (subsidy : Nat → Int) (blocks : List (List (Tx T))) (h : Nat)
    (u' : UtxoSet T) (hnd : ∀ b ∈ blocks, (b.map Tx.txid).Nodup)
    (hc : connectChain subsidy [] h blocks = some u') :
    totalValue u' ≤ subsidySum subsidy h blocks.length := by
  have := BitcoinUtxo.chain_bound subsidy blocks [] h u' List.nodup_nil hnd hc
  have h0 : totalValue ([] : UtxoSet T) = 0 := rfl
  rw [h0] at this
  omega
