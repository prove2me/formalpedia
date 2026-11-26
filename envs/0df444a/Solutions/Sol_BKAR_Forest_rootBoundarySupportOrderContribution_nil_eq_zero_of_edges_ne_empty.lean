-- Prove2me | solution 1 for BKAR.Forest.rootBoundarySupportOrderContribution_nil_eq_zero_of_edges_ne_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:53:37.727618+00:00
-- url     : https://prove2.me/submissions/525ff107-3ea2-4bf0-aef0-5354112f1306

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_empty_order_eq_zero
import Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V)
    (hI : I.edges ≠ ∅) :
    rootBoundarySupportOrderContribution choices ρ I [] = 0 := by
  rw [rootBoundarySupportOrderContribution_eq_treeFiber_of_edges_ne_empty
    choices ρ I [] hI]
  exact boundarySupportOrderTreeFiber_empty_order_eq_zero choices I ρ
end BKAR.Forest
