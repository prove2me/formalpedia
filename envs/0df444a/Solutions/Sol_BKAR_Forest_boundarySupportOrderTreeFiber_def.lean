-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiber_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:03:11.55396+00:00
-- url     : https://prove2.me/submissions/e236b1b0-1825-4ba7-9614-e4fbcdc3820c

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
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (I : ForestIndex V) (order : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeFiber choices F pref prefixTs top I order ρ =
      localBoundarySupportOrderContribution choices F pref prefixTs top
        I order ρ +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeFiber choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
              t I order ρ) := by
  rw [boundarySupportOrderTreeFiber]
end BKAR.Forest
