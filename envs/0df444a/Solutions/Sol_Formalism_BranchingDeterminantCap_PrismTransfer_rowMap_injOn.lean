-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.rowMap_injOn
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:22.616985+00:00
-- url     : https://prove2.me/submissions/c5b4dd7c-d0e1-4804-9bcf-6afb982a8d33

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_rowMap_apply

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
theorem _root_.solution {n : ℕ} (G : ℕ) (hG : 0 < G) (x : Fin n → V →ₗ[K] V) (A : Submodule (𝓞 K) V)
    (h : ∀ a : Fin n → V, (∀ i, a i ∈ A) → ∑ i, x i (a i) = 0 → a = 0) :
    Set.InjOn (rowMap ((G : K) ^ 3) x) ((Submodule.pi Set.univ fun _ : Fin n => A : Submodule (𝓞 K) (Fin n → V)) : Set (Fin n → V)) := by
  intro a₁ ha₁ a₂ ha₂ hEq
  have hsub : a₁ - a₂ ∈ (Submodule.pi Set.univ fun _ : Fin n => A) := sub_mem ha₁ ha₂
  rw [Submodule.mem_pi] at hsub
  refine sub_eq_zero.mp (h _ (fun i => hsub i (Set.mem_univ i)) ?_)
  have h2 : rowMap ((G : K) ^ 3) x (a₁ - a₂) = 0 := by rw [map_sub, hEq, sub_self]
  rw [rowMap_apply, ← Finset.smul_sum] at h2
  exact (smul_eq_zero.mp h2).resolve_left (pow_ne_zero 3 (Nat.cast_ne_zero.mpr hG.ne'))
end Formalism.BranchingDeterminantCap.PrismTransfer
