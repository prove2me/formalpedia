-- Prove2me | solution 1 for BraidsLinksMCG.cor_1_8_1_pure_braid_semidirect
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T18:15:13.272899+00:00
-- url     : https://prove2.me/submissions/9599ccf9-b821-4656-9069-f0e4639f1dca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_puncturedPlaneGroup_equiv_free
import Theorems.Thm_BraidsLinksMCG_pureBraid_forget_section
import Mathlib
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

theorem _root_.solution (n : ℕ) :
    Nonempty (PuncturedPlaneGroup n ≃* FreeGroup (Fin n)) ∧
      ∃ s : PureBraidGroup n →* PureBraidGroup (n + 1),
        (FundamentalGroup.mapOfEq (configForget n) (configForget_base n)).comp s =
          MonoidHom.id (PureBraidGroup n) :=
  ⟨BraidsLinksMCG.puncturedPlaneGroup_equiv_free n,
   BraidsLinksMCG.pureBraid_forget_section n⟩

#print axioms solution
