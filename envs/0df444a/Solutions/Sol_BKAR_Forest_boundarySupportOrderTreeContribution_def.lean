-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeContribution_def
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:00:58.691176+00:00
-- url     : https://prove2.me/submissions/6c2db041-0199-4b7c-885d-f22fce73e53a

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
      localBoundarySupportOrderSum choices F pref prefixTs top ρ +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            boundarySupportOrderTreeContribution choices
              (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) := by
  rw [boundarySupportOrderTreeContribution]
end BKAR.Forest
