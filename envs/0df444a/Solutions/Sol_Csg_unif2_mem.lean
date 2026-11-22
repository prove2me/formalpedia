-- Prove2me | solution 1 for Csg.unif2_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:11:57.275274+00:00
-- url     : https://prove2.me/submissions/2c9f4f73-f54c-44f1-adfe-3a40feadb8c8

import Definitions.Def_Csg_BackwardInduction
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_MatchingPennies
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : unif2 ∈ stdSimplex ℝ (Fin 2) :=
  ⟨fun i => by simp only [unif2]; norm_num, by simp only [unif2, Fin.sum_univ_two]; norm_num⟩
end Csg
