-- Prove2me | solution 1 for BitcoinUniqueness.coinbase_height_prefix
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-29T13:58:44.841988+00:00
-- url     : https://prove2.me/submissions/886bf57a-4164-4be6-97a9-15f0b90d9756

import Definitions.Def_BitcoinUniqueness
import Definitions.Def_BitcoinSer
import Definitions.Def_BitcoinHeader
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
    (h34 : BitcoinHeader.BIP34Height ≤ S.nextHeight) :
    (BitcoinBlockV2.heightScript S.nextHeight).isPrefixOf (BitcoinUniqueness.coinbaseScriptSig b) = true := by
  obtain ⟨hcc, _⟩ := s229_validate_accept_inv h
  have hact : BitcoinActivation.activeAfter S.tipHeight .heightInCB = true := by
    unfold BitcoinActivation.activeAfter ChainState.tipHeight
    unfold ChainState.nextHeight BitcoinHeader.BIP34Height at h34
    simp [BitcoinActivation.deploymentHeight]; omega
  unfold contextualCheckBlock at hcc
  simp only [hact, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hcc
  exact hcc.1.1.2
