-- Prove2me | solution 2 for BraidsLinksMCG.last_standard_pure_word_eval_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T21:18:15.490157+00:00
-- url     : https://prove2.me/submissions/4412177a-cb56-4e01-949e-f1e8804e9a1f

import Mathlib
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Theorems.Thm_TarchaBraids_standardPureBraidWord_last_eval_v1

open TarchaBraids

theorem solution (n : Nat) :
    FreeGroup.lift (fun i : Fin (n + 2 - 1) => halfTwistBraid (n + 2) i)
      (braidWordFree (standardPureBraidWord (n + 1) (Fin.last n)))
      = (halfTwistBraid (n + 2) (Fin.last n)) ^ 2 := by
  have hfin : (⟨n, by omega⟩ : Fin (n + 1)) = Fin.last n := by
    apply Fin.ext
    rfl
  simpa only [hfin] using TarchaBraids.standardPureBraidWord_last_eval_v1 n
