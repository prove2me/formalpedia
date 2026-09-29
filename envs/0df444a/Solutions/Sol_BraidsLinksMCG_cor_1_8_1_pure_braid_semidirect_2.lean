-- Prove2me | solution 2 for BraidsLinksMCG.cor_1_8_1_pure_braid_semidirect
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-23T05:51:48.747221+00:00
-- url     : https://prove2.me/submissions/38d40b22-9ca6-4404-b2db-f2f37cec72cb
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace
import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_equiv_free
import Theorems.Thm_BraidsLinksMCG_pureBraid_forget_section

open BraidsLinksMCG

/-- Corollary 1.8.1 (pure braid splitting), assembled from its two published ingredients:
the freeness of the punctured-plane group and the splitting section of the forgetful map. -/
theorem solution (n : ℕ) :
    Nonempty (PuncturedPlaneGroup n ≃* FreeGroup (Fin n)) ∧
      ∃ s : PureBraidGroup n →* PureBraidGroup (n + 1),
        (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp s =
          MonoidHom.id (PureBraidGroup n) :=
  ⟨puncturedPlaneGroup_equiv_free n, pureBraid_forget_section n⟩
