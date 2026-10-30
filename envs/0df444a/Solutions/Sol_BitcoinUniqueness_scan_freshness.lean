-- Prove2me | solution 1 for BitcoinUniqueness.scan_freshness
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:58:43.442407+00:00
-- url     : https://prove2.me/submissions/470c5711-ebbe-4b40-8829-857b89aad903

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
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

theorem solution (S : ChainState) (b : BitcoinSer.Block) (now : Int) (S' : ChainState)
    (undo : BlockUndo) (hR : BitcoinBlockV2.Reachable S) (h : BitcoinBlockV2.validate S b now = .accept S' undo)
    (hscan : BitcoinUniqueness.ScanRuns S b) (hg : BitcoinSer.headerHash b.header ≠ BitcoinSer.genesisHash) :
    BitcoinUniqueness.FreshOutputs S.utxo b := by
  obtain ⟨_, u, hc, _⟩ := s229_validate_accept_inv h
  unfold ScanRuns at hscan
  unfold connectBlock at hc
  simp only [hg, if_false, hscan, Bool.true_and] at hc
  have hok : bip30Ok S.utxo b = true := by
    cases hk : bip30Ok S.utxo b
    · simp [hk] at hc
    · rfl
  intro tx htx o ho
  unfold bip30Ok at hok
  rw [List.all_eq_true] at hok
  have := hok tx htx
  rw [List.all_eq_true] at this
  have := this o (List.mem_range.2 ho)
  simpa [haveCoin] using this

