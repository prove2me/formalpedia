-- Prove2me | solution 1 for BKAR.Forest.TerminalGrowth.ofActiveEdgesEqEmpty_branchIntegralAux
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:55:40.029844+00:00
-- url     : https://prove2.me/submissions/36a28aaf-e431-4cb5-8c25-866d01214baf

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil



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
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (ofActiveEdgesEqEmpty F hF).branchIntegralAux top u ρ =
      ρ (F.standardInterp u) :=
  OrderedGrowth.branchIntegralAux_nil top F u ρ
end BKAR.Forest.TerminalGrowth
