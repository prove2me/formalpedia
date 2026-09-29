-- Prove2me | solution 1 for BraidsLinksMCG.standardGen_image_eq_classical_halfTwist_word_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T07:23:23.610471+00:00
-- url     : https://prove2.me/submissions/ee9573d8-708c-4aeb-9fd1-513b483f4701
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_generation_word_data_v1
import Definitions.Def_TarchaBraids_standard_pure_braid_word_v1
import Definitions.Def_TarchaBraids_strand_extension_v1
import Theorems.Thm_BraidsLinksMCG_standardGen_image_last_eq_last_halfTwist_square_v1
import Theorems.Thm_BraidsLinksMCG_standardGen_image_strandExtension_conjugate_v1
import Theorems.Thm_TarchaBraids_standardPureBraidWord_eval_transport_v2
import Theorems.Thm_TarchaBraids_standardPureBraidWord_last_eval_v1

open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

theorem solution (n : ℕ) (j : Fin n) :
    (FundamentalGroup.map (configProj (n + 1)) (baseOrdered (n + 1)))
        ((FundamentalGroup.mapOfEq (configIncl n) (configIncl_base n)) (standardGen n j))
      =
    FreeGroup.lift
      (fun i : Fin (n + 1 - 1) => halfTwistBraid (n + 1) i)
      (braidWordFree (standardPureBraidWord n j)) := by
  induction n with
  | zero =>
      exact Fin.elim0 j
  | succ n ih =>
      induction j using Fin.lastCases with
      | last =>
          rw [standardGen_image_last_eq_last_halfTwist_square_v1 n]
          rw [standardPureBraidWord_last_eval_v1 n]
          have h_index :
              Fin.last n = (⟨n, by omega⟩ : Fin (n + 2 - 1)) := by
            apply Fin.ext
            rfl
          rw [h_index]
          rfl
      | cast j =>
          rw [standardGen_image_strandExtension_conjugate_v1 n j]
          rw [ih j]
          rw [← standardPureBraidWord_eval_transport_v2 n j]
