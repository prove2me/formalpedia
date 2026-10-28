-- Prove2me | solution 1 for BitcoinUtxo.chain_bound
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:09.415765+00:00
-- url     : https://prove2.me/submissions/39285cae-92b4-4e71-9eab-4009b42f0750

import Definitions.Def_BitcoinUtxo
import Theorems.Thm_BitcoinUtxo_block_bound

open BitcoinUtxo

private theorem subsidySum_succ_left (s : Nat → Int) :
    ∀ (n h : Nat), subsidySum s h (n + 1) = s h + subsidySum s (h + 1) n
  | 0, h => by simp [subsidySum]
  | n + 1, h => by
    have ih := subsidySum_succ_left s n h
    unfold subsidySum
    rw [ih]
    have e : h + (n + 1) = h + 1 + n := by omega
    rw [e]
    unfold subsidySum
    omega

theorem solution {T : Type} [DecidableEq T] (subsidy : Nat → Int) :
    ∀ (blocks : List (List (Tx T))) (u : UtxoSet T) (h : Nat) (u' : UtxoSet T),
      keysNodup u → (∀ b ∈ blocks, (b.map Tx.txid).Nodup) →
      connectChain subsidy u h blocks = some u' →
      totalValue u' ≤ totalValue u + subsidySum subsidy h blocks.length
  | [], u, h, u', _, _, hc => by
    simp only [connectChain, Option.some.injEq] at hc
    subst hc
    simp [subsidySum]
  | b :: rest, u, h, u', hn, hnd, hc => by
    unfold connectChain at hc
    cases hb : connectBlock subsidy u h b with
    | none => rw [hb] at hc; simp at hc
    | some p =>
      obtain ⟨u1, fees⟩ := p
      rw [hb] at hc
      simp only [] at hc
      obtain ⟨h1, hn1⟩ := BitcoinUtxo.block_bound subsidy u h b u1 fees hn (hnd b (List.mem_cons_self ..)) hb
      have ih := solution subsidy rest u1 (h + 1) u' hn1
        (fun b' hb' => hnd b' (List.mem_cons_of_mem _ hb')) hc
      rw [List.length_cons, subsidySum_succ_left]
      omega
