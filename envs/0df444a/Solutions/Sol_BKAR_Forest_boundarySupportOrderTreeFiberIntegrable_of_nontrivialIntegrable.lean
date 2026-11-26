-- Prove2me | solution 1 for BKAR.Forest.boundarySupportOrderTreeFiberIntegrable_of_nontrivialIntegrable
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:49:05.163152+00:00
-- url     : https://prove2.me/submissions/e04d4ba1-ef2c-42e7-9820-e047e85d5e32

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
import Theorems.Thm_BKAR_Forest_boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegralAux_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegral_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_branchIntegrand_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_derivativeOrder_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_cons
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_cons_nil
import Theorems.Thm_BKAR_Forest_OrderedGrowth_params_nil
import Theorems.Thm_BKAR_Forest_edgeSetOrders_empty
import Theorems.Thm_BKAR_Forest_emptyActiveEdge_val
import Theorems.Thm_BKAR_Forest_paramValue_of_mem
import Theorems.Thm_BKAR_Forest_pathMin_cons
import Theorems.Thm_BKAR_Forest_pathMin_nil
import Theorems.Thm_BKAR_edgeBasis_self
import Theorems.Thm_BKAR_mixedPartialList_cons
import Theorems.Thm_BKAR_mixedPartialList_cons_apply
import Theorems.Thm_BKAR_mixedPartialList_nil
import Theorems.Thm_BKAR_mixedPartialList_nil_apply
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_cons
import Theorems.Thm_BKAR_orderedSimplexIntegralAux_nil
import Theorems.Thm_BKAR_orderedSimplexIntegral_cons
import Theorems.Thm_BKAR_orderedSimplexIntegral_nil
import Theorems.Thm_BKAR_orderedSimplexParams_cons
import Theorems.Thm_BKAR_orderedSimplexParams_nil
import Theorems.Thm_BKAR_updateCoord_same_value
import Theorems.Thm_BKAR_updateCoord_self
import Theorems.Thm_BKAR_updateCoord_update_same
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegralAux_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegral_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.branchIntegrand_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.derivativeOrder_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_cons
attribute [local simp] BKAR.Forest.OrderedGrowth.params_cons_nil
attribute [local simp] BKAR.Forest.OrderedGrowth.params_nil
attribute [local simp] BKAR.Forest.emptyActiveEdge_val
attribute [local simp] BKAR.Forest.paramValue_of_mem
attribute [local simp] BKAR.Forest.pathMin_cons
attribute [local simp] BKAR.Forest.pathMin_nil
attribute [local simp] BKAR.edgeBasis_self
attribute [local simp] BKAR.mixedPartialList_cons
attribute [local simp] BKAR.mixedPartialList_cons_apply
attribute [local simp] BKAR.mixedPartialList_nil
attribute [local simp] BKAR.mixedPartialList_nil_apply
attribute [local simp] BKAR.orderedSimplexIntegralAux_cons
attribute [local simp] BKAR.orderedSimplexIntegralAux_nil
attribute [local simp] BKAR.orderedSimplexIntegral_cons
attribute [local simp] BKAR.orderedSimplexIntegral_nil
attribute [local simp] BKAR.orderedSimplexParams_cons
attribute [local simp] BKAR.orderedSimplexParams_nil
attribute [local simp] BKAR.updateCoord_same_value
attribute [local simp] BKAR.updateCoord_self
attribute [local simp] BKAR.updateCoord_update_same



set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKAR.Forest
theorem _root_.solution
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      boundarySupportOrderTreeFiberNontrivialIntegrable choices n
        F pref prefixTs top ρ →
      boundarySupportOrderTreeFiberIntegrable choices n
        F pref prefixTs top ρ
  | 0, _F, _pref, _prefixTs, _top, _ρ, _hcore => by
      trivial
  | n + 1, F, pref, prefixTs, top, ρ, hcore => by
      rcases hcore with ⟨hInt, hchild⟩
      constructor
      · intro e x hx
        by_cases hlen : x.2.length ≤ (pref ++ [e.val]).length
        · have hzero :
              (fun t : ℝ =>
                boundarySupportOrderTreeFiber choices
                  (choices F e).forest (pref ++ [e.val])
                  (prefixTs ++ [t]) t x.1 x.2 ρ) = fun _ => 0 := by
            funext t
            exact
              boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
                choices (choices F e).forest.activeEdges.card
                (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t])
                t x.1 x.2 ρ le_rfl hlen
          rw [hzero]
          exact continuous_const.intervalIntegrable 0 top
        · have hlt : (pref ++ [e.val]).length < x.2.length :=
            Nat.lt_of_not_ge hlen
          have hxmem := hx
          rw [supportOrderPairs, Finset.mem_sigma] at hxmem
          by_cases hI : x.1.edges = ∅
          · have horder_nil : x.2 = [] := by
              have horder' :
                  x.2 ∈ edgeSetOrders (∅ : Finset (Edge V)) := by
                simpa [hI] using hxmem.2
              rw [edgeSetOrders_empty] at horder'
              exact Finset.mem_singleton.mp horder'
            have hzero :
                (fun t : ℝ =>
                  boundarySupportOrderTreeFiber choices
                    (choices F e).forest (pref ++ [e.val])
                    (prefixTs ++ [t]) t x.1 x.2 ρ) = fun _ => 0 := by
              funext t
              rw [horder_nil]
              exact
                boundarySupportOrderTreeFiber_eq_zero_of_order_length_le_pref_length
                  choices (choices F e).forest.activeEdges.card
                  (choices F e).forest (pref ++ [e.val])
                  (prefixTs ++ [t]) t x.1 [] ρ le_rfl (by simp)
            rw [hzero]
            exact continuous_const.intervalIntegrable 0 top
          · exact hInt e x hx hlt hI
      · intro e t ht
        exact
          solution
            choices n (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t ρ (hchild e t ht)
end BKAR.Forest
