-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:04:15.76703+00:00
-- url     : https://prove2.me/submissions/d0d0e19c-afb2-4b14-825b-9562c9b91a2d

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (order : List (Edge V)) :
    rootBoundarySupportOrderContribution choices ρ I order =
      (if I.edges = ∅ ∧ order = [] then ρ zeroConfig else 0) +
        boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
          I order ρ :=
  rfl
end BKAR.Forest
