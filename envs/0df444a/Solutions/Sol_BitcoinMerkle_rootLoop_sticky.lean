-- Prove2me | solution 1 for BitcoinMerkle.rootLoop_sticky
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:01.414155+00:00
-- url     : https://prove2.me/submissions/41e4a4bc-32d6-4fc0-a97e-3faef873f79a

import Definitions.Def_BitcoinMerkle

open BitcoinMerkle

/-- One iteration of the loop. -/
private theorem rootLoop_step {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = BitcoinMerkle.rootLoop c z (BitcoinMerkle.pairUp c hs) (m || BitcoinMerkle.hasEqualPair hs) := by
  conv => lhs; rw [rootLoop]
  rw [dif_pos h]

/-- Loop exit. -/
private theorem rootLoop_stop {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m : Bool) (h : ¬ 1 < hs.length) :
    BitcoinMerkle.rootLoop c z hs m = (hs.headD z, m) := by
  rw [rootLoop, dif_neg h]

/-- Once set, the flag stays set. -/
theorem solution {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) : (BitcoinMerkle.rootLoop c z hs true).2 = true := by
  by_cases h : 1 < hs.length
  · rw [rootLoop_step c z hs true h]
    simp only [Bool.true_or]
    exact solution c z (pairUp c hs)
  · rw [rootLoop_stop c z hs true h]
termination_by hs.length
decreasing_by
  simp_wf
  rw [pairUp_length]
  omega
