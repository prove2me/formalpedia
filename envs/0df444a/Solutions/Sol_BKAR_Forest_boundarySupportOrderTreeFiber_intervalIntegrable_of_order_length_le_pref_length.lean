-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_le_pref_length
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:47:37.276976+00:00
-- url     : https://prove2.me/submissions/aa880749-c8d0-4d2f-96d5-fe96f55abdeb

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length

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
    (ρ : (Edge V → ℝ) → ℝ)
    (hlen : order.length ≤ pref.length) :
    IntervalIntegrable
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices F pref prefixTs t I order ρ)
      MeasureTheory.volume 0 top := by
  have hzero :
      (fun t : ℝ =>
        boundarySupportOrderTreeFiber choices F pref prefixTs t I order ρ) =
        fun _ => 0 := by
    funext t
    exact
      boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
        choices F.activeEdges.card F pref prefixTs t I order ρ le_rfl hlen
  rw [hzero]
  exact continuous_const.intervalIntegrable 0 top
end BKAR.Forest
