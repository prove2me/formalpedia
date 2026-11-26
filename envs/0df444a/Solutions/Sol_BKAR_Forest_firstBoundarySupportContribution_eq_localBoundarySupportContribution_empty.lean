-- Prove2me | solution 1 for BKAR.Forest.firstBoundarySupportContribution_eq_localBoundarySupportContribution_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:32:35.845663+00:00
-- url     : https://prove2.me/submissions/88de7af1-9fa3-4dda-85ec-f24bdc2a9d33

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_Forest_localBoundarySupportContribution_def
import Theorems.Thm_BKAR_Forest_firstBoundarySupportContribution_def
import Theorems.Thm_BKAR_Forest_integral_standardInterp_empty_singleton_eq_orderedContribution


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (I : ForestIndex V) (ρ : (Edge V → ℝ) → ℝ) :
    firstBoundarySupportContribution choices I ρ =
      localBoundarySupportContribution choices (Forest.empty V) [] [] 1 I ρ := by
  rw [firstBoundarySupportContribution_def,
    localBoundarySupportContribution_def]
  apply Finset.sum_congr rfl
  intro e _
  rw [← integral_standardInterp_empty_singleton_eq_orderedContribution]
  rfl
end BKAR.Forest
