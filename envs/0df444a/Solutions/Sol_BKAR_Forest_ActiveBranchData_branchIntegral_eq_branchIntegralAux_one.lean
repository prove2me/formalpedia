-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.branchIntegral_eq_branchIntegralAux_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:41:59.21403+00:00
-- url     : https://prove2.me/submissions/4263ac0a-72e7-441c-803c-318a9602df2a

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveBranchData
theorem _root_.solution (data : ActiveBranchData F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ = data.branchIntegralAux 1 u ρ :=
  rfl
end BKAR.Forest.ActiveBranchData
