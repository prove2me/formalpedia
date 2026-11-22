-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.colMap_map_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:39.616325+00:00
-- url     : https://prove2.me/submissions/4ca04e87-4a5d-43e7-8193-b00b791db1db

import Mathlib
import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_TransferMean
import Definitions.Def_Formalism_MeanHeightDescent_AverageDegreeBounds_GoodBadCut
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_Transfer
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_colMap_apply
import Theorems.Thm_Formalism_BranchingDeterminantCap_PrismTransfer_pow_smul_eq

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
theorem _root_.solution {n : ℕ} (G : ℕ) (xs : Fin n → V →ₗ[K] V) (A B : Submodule (𝓞 K) V)
    (h : ∀ i, ∀ c ∈ B, ((G : 𝓞 K) ^ 3) • xs i c ∈ A) :
    B.map ((colMap ((G : K) ^ 3) xs).restrictScalars (𝓞 K)) ≤
      Submodule.pi Set.univ fun _ : Fin n => A := by
  intro y hy
  obtain ⟨c, hc, rfl⟩ := Submodule.mem_map.mp hy
  rw [Submodule.mem_pi]
  intro i _
  change colMap ((G : K) ^ 3) xs c i ∈ A
  rw [colMap_apply, ← PrismTransfer.pow_smul_eq]
  exact h i c hc
end Formalism.BranchingDeterminantCap.PrismTransfer
