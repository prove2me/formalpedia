-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.ofActiveEdgesEqEmpty_branchIntegral
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:23:20.97083+00:00
-- url     : https://prove2.me/submissions/28615b96-9cfc-4664-a478-4e1673e5edc7

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_TerminalGrowth_ofActiveEdgesEqEmpty_branchIntegralAux

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}
namespace BKAR.Forest.TerminalGrowth
theorem _root_.solution
    (F : Forest V) (hF : F.activeEdges = ∅)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (ofActiveEdgesEqEmpty F hF).branchIntegral u ρ =
      ρ (F.standardInterp u) :=
  ofActiveEdgesEqEmpty_branchIntegralAux F hF 1 u ρ
end BKAR.Forest.TerminalGrowth
