-- Prove2me | solution 1 for BKAR.Forest.firstRecursiveBoundaryRemainder_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:15:15.769835+00:00
-- url     : https://prove2.me/submissions/daa2e9ff-6003-45f0-88aa-3b2e3aaa48df

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
    (ρ : (Edge V → ℝ) → ℝ) :
    firstRecursiveBoundaryRemainder choices ρ =
      Finset.sum (Forest.empty V).activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ)) :=
  rfl
end BKAR.Forest
