-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeContribution_eq_sum_treeFiber_of_activeEdges_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:52:24.834603+00:00
-- url     : https://prove2.me/submissions/16c06b90-0508-4674-8be3-f7b87fa81a02

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V)
    (n : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hle : F.activeEdges.card ≤ n)
    (hfiber :
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ) :
    boundarySupportOrderTreeContribution choices F pref prefixTs top ρ =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            boundarySupportOrderTreeFiber choices F pref prefixTs top
              I order ρ)) := by
  have h :=
    boundarySupportOrderTreeContribution_eq_sum_supportOrderPairs_treeFiber_of_activeEdges_card_le
      choices n F pref prefixTs top ρ hle hfiber
  rw [supportOrderPairs, Finset.sum_sigma] at h
  exact h
end BKAR.Forest
