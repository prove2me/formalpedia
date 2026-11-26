-- Prove2me | solution 1 for BKAR.BKARContDiff.boundarySupportOrderTreeFiber_intervalIntegrable_of_order_length_eq_pref_length_add
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:37:17.162649+00:00
-- url     : https://prove2.me/submissions/bd3aa0fc-5135-44f6-964f-96a9426dfa44

import Definitions.Def_BKAR_CubePartition_Smoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Theorems.Thm_BKAR_BKARContDiff_boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
import Theorems.Thm_BKAR_ListPathContinuous_const


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
namespace BKAR.BKARContDiff
theorem _root_.solution
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (k : Nat) (F : Forest V) (pref : List (Edge V))
    (prefixTs : List ℝ) (I : ForestIndex V) (order : List (Edge V))
    (top : ℝ)
    (hprefixTs : prefixTs.length = pref.length)
    (hlen : order.length = pref.length + k) :
    IntervalIntegrable
      (fun t : ℝ =>
        Forest.boundarySupportOrderTreeFiber choices F pref prefixTs t
          I order ρ)
      MeasureTheory.volume 0 top := by
  have hts :
      BKAR.ListPathContinuous pref.length
        (fun _ : ℝ => prefixTs) := by
    rw [← hprefixTs]
    exact BKAR.ListPathContinuous.const prefixTs
  exact
    (boundarySupportOrderTreeFiber_continuous_comp_of_order_length_eq_pref_length_add
      hρ choices k F pref hts continuous_id I order hlen).intervalIntegrable 0 top
end BKAR.BKARContDiff
