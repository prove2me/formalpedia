-- Prove2me | solution 1 for BKAR.Forest.ActiveTerminalBranchData.singleton_branchIntegral_eq_activeBranchData_singleton
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:26:30.642888+00:00
-- url     : https://prove2.me/submissions/bf146b45-b47d-4d00-ac7b-fe9fc43dcdb6

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveTerminalBranchData
theorem _root_.solution
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (singleton extensions hterm).branchIntegral u ρ =
      (ActiveBranchData.singleton extensions).branchIntegral u ρ :=
  rfl
end BKAR.Forest.ActiveTerminalBranchData
