-- Prove2me | solution 1 for BraidsLinksMCG.standardGen_image_last_eq_last_halfTwist_square_v1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-23T19:55:56.569367+00:00
-- url     : https://prove2.me/submissions/0c98821f-b86a-49ba-831c-d51ca9348dac
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Definitions.Def_BraidsLinksMCG_StandardLoops
import Definitions.Def_TarchaBraids_HalfTwist
import Definitions.Def_TarchaBraids_strand_extension_v1
import Theorems.Thm_BraidsLinksMCG_standardGen_image_eq_classical_halfTwist_word_v1
import Theorems.Thm_BraidsLinksMCG_last_standard_pure_word_eval_v2
open BraidsLinksMCG TarchaBraids TarchaBraids.StrandExtension

theorem solution (n : Nat) :
    (FundamentalGroup.map (configProj (n + 2)) (baseOrdered (n + 2)))
      ((FundamentalGroup.mapOfEq (configIncl (n + 1)) (configIncl_base (n + 1)))
        (standardGen (n + 1) (Fin.last n)))
      = (halfTwistBraid (n + 2) (Fin.last n)) ^ 2 := by
  rw [standardGen_image_eq_classical_halfTwist_word_v1 (n + 1) (Fin.last n)]
  exact last_standard_pure_word_eval_v2 n
