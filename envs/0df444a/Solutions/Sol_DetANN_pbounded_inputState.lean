-- Prove2me | solution 1 for DetANN.pbounded_inputState
-- status  : ACCEPTED   (prove)
-- author  : @milia
-- created : 2026-11-15T08:19:08.783233+00:00
-- url     : https://prove2.me/submissions/df72b7ce-13e1-43cc-a2cd-10dab52aec6b

import Mathlib
import Definitions.Def_PNormReg_Machine
import Definitions.Def_PNormRegLib_AddressBound
import Definitions.Def_DetANN_DataStructure

open DetANN

theorem solution {N m : ℕ} (Y : Fin N → EuclideanSpace ℝ (Fin m)) (θ : ℝ) :
    PNormRegLib.PBounded ((N : ℤ) + m + 1) (inputState Y θ) := by
  refine ⟨fun q => by simp [inputState, PNormReg.initState]; positivity, fun z => ?_⟩
  simp only [inputState, PNormReg.initState]
  split_ifs
  · generalize z.toNat = n
    rcases n with _ | _ | n
    · simp; omega
    · simp; omega
    · simp; omega
  · simp; omega
