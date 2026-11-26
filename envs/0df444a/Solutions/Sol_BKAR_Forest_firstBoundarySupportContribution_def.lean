-- Prove2me | solution 1 for BKAR.Forest.firstBoundarySupportContribution_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T08:59:15.406595+00:00
-- url     : https://prove2.me/submissions/f57b38a0-d01e-4ece-82d1-3da90ebf1ac5

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping

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
      Finset.sum
        ((Forest.empty V).activeEdges.attach.filter
          (fun e => (choices (Forest.empty V) e).forest.support = I))
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) := by
  rw [firstBoundarySupportContribution]
end BKAR.Forest
