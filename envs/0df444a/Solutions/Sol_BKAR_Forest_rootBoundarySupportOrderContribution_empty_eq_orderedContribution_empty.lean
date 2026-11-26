-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:18:56.526434+00:00
-- url     : https://prove2.me/submissions/1964b6cb-8c3a-4b42-b0cc-4d23c599a6a6

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_empty_order_eq_zeroConfig
import Theorems.Thm_BKAR_Forest_orderedContribution_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (hI : I.edges = ∅) :
    rootBoundarySupportOrderContribution choices ρ I [] =
      (Forest.empty V).orderedContribution [] ρ := by
  rw [rootBoundarySupportOrderContribution_empty_order_eq_zeroConfig
    choices ρ I hI]
  rw [orderedContribution_empty]
end BKAR.Forest
