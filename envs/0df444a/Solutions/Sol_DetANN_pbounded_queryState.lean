-- Prove2me | solution 1 for DetANN.pbounded_queryState
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:20:43.086497+00:00
-- url     : https://prove2.me/submissions/723ed73e-bb6d-47b1-9318-c05c4728d2e6

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure

open DetANN

theorem solution (X : ℤ) (s : PNormReg.State) (hs : PNormRegLib.PBounded X s)
    (hX : 0 ≤ X) (m : ℕ) (q : EuclideanSpace ℝ (Fin m)) :
    PNormRegLib.PBounded X (queryState m s q) :=
  ⟨fun _ => by simpa [queryState] using hX, fun z => by simpa [queryState] using hs.2 z⟩
