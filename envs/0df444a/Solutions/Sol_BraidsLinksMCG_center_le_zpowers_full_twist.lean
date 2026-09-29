-- Prove2me | solution 1 for BraidsLinksMCG.center_le_zpowers_full_twist
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T20:55:30.856533+00:00
-- url     : https://prove2.me/submissions/5cd7e54e-7394-41ea-ae94-0c5bef2e078a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_BraidsLinksMCG_pure_center_le_zpowers_full_twist
import Theorems.Thm_BraidsLinksMCG_center_le_ker_perm
import Theorems.Thm_BraidsLinksMCG_braid_perm_hom
import Mathlib
import Definitions.Def_BraidsLinksMCG_ArtinBraidGroup
import Definitions.Def_BraidsLinksMCG_ArtinEndo

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option linter.all false

open BraidsLinksMCG

theorem _root_.solution (n : ℕ) (hn : 3 ≤ n) :
    Subgroup.center (ArtinBraidGroup n) ≤ Subgroup.zpowers (sigmaProd n ^ n) := by
  obtain ⟨pi, hpi⟩ := BraidsLinksMCG.braid_perm_hom n
  intro b hb
  have hpure : pi b = 1 := BraidsLinksMCG.center_le_ker_perm n hn pi hpi hb
  exact BraidsLinksMCG.pure_center_le_zpowers_full_twist n hn pi hpi b hb hpure

#print axioms solution
