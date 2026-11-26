-- Prove2me | solution 1 for BKAR.Forest.firstBoundarySupportOrderContribution_eq_localBoundarySupportOrderContribution_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:36.446795+00:00
-- url     : https://prove2.me/submissions/fdf9cc90-6cda-47c4-850f-7b6b1b3d3915

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_localBoundarySupportOrderContribution_def
import Theorems.Thm_BKAR_Forest_firstBoundarySupportOrderContribution_def
import Theorems.Thm_BKAR_Forest_integral_standardInterp_empty_singleton_eq_orderedContribution


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportOrderContribution choices I order ρ =
      localBoundarySupportOrderContribution choices (Forest.empty V) [] [] 1
        I order ρ := by
  rw [firstBoundarySupportOrderContribution_def,
    localBoundarySupportOrderContribution_def]
  apply Finset.sum_congr rfl
  intro e he
  rw [← (Finset.mem_filter.mp he).2.2]
  rw [← integral_standardInterp_empty_singleton_eq_orderedContribution]
  rfl
end BKAR.Forest
