-- Prove2me | solution 1 for BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_partialDeriv_interpWithFill_of_activeEdges_eq_empty
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T09:21:20.958019+00:00
-- url     : https://prove2.me/submissions/ec573503-12f8-448f-afdb-6301358db8ae

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
import Theorems.Thm_BKAR_Forest_ActiveExtension_singletonGrowth_branchIntegralAux_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty


set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}
namespace BKAR.Forest.ActiveBranchData
theorem _root_.solution
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (top : ℝ) (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegralAux top u ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          partialDeriv e.val ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by
  rw [branchIntegralAux]
  apply Finset.sum_congr rfl
  intro e _
  exact (extensions e).singletonGrowth_branchIntegralAux_eq_integral_partialDeriv_interpWithFill_of_activeEdges_eq_empty
    top u ρ (hterm e)
end BKAR.Forest.ActiveBranchData
