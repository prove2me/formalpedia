-- Prove2me | solution 1 for BraidsLinksMCG.thm_1_8_artin_presentation
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T17:53:18.655467+00:00
-- url     : https://prove2.me/submissions/7bcf2a4c-0dbe-41fb-868c-b1d5628e4e7a

import Theorems.Thm_TarchaBraids_thm_3_15_artin_presentation
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ConfigSpace

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

theorem _root_.solution (n : ℕ) :
    Nonempty (ArtinBraidGroup n ≃* GeomBraidGroup n) :=
  ⟨(TarchaBraids.thm_3_15_artin_presentation n).choose⟩

#print axioms solution
