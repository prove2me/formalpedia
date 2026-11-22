-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.colMap_injOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:26:20.793358+00:00
-- url     : https://prove2.me/submissions/6e5731bd-14a8-4c00-90ef-fc4ffc87f153

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_colMap_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
open scoped Matrix
noncomputable section
open Formalism Formalism.BranchingDeterminantCap
open Formalism.HN
open PrismTransfer
open Formalism.BranchingDeterminantCap.PrismTransfer
variable {K : Type} [Field K] [NumberField K] [StarRing K]
  {V ι : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.PrismTransfer
theorem _root_.solution {n : ℕ} (G : ℕ) (hG : 0 < G) (xs : Fin n → V →ₗ[K] V) (B : Submodule (𝓞 K) V)
    (h : ∀ c ∈ B, (∀ i, xs i c = 0) → c = 0) :
    Set.InjOn (colMap ((G : K) ^ 3) xs) (B : Set V) := by
  intro y₁ hy₁ y₂ hy₂ hxy
  refine sub_eq_zero.mp (h _ (sub_mem hy₁ hy₂) fun i => ?_)
  have hi := congrFun hxy i
  rw [colMap_apply, colMap_apply] at hi
  rw [map_sub, sub_eq_zero]
  exact smul_right_injective V (pow_ne_zero 3 (Nat.cast_ne_zero.mpr hG.ne')) hi
end Formalism.BranchingDeterminantCap.PrismTransfer
