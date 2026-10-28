-- Prove2me | solution 1 for BitcoinMerkle.rootLoop_fst
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-10-26T04:37:00.81824+00:00
-- url     : https://prove2.me/submissions/b19c2895-23c0-45b5-98f5-6a0d2b208b3a

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

/-- The root does not depend on the incoming flag. -/
theorem solution {H : Type} [DecidableEq H] (c : H → H → H) (z : H)
    (hs : List H) (m m' : Bool) : (BitcoinMerkle.rootLoop c z hs m).1 = (BitcoinMerkle.rootLoop c z hs m').1 := by
  by_cases h : 1 < hs.length
  · rw [rootLoop_step c z hs m h, rootLoop_step c z hs m' h]
    exact solution c z (pairUp c hs) _ _
  · rw [rootLoop_stop c z hs m h, rootLoop_stop c z hs m' h]
termination_by hs.length
decreasing_by
  simp_wf
  rw [pairUp_length]
  omega
