-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.PrismTransfer.toMatrix_colMap
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:22.891676+00:00
-- url     : https://prove2.me/submissions/5d3aa2d3-49a3-4309-a3c4-4cf6644ed3a7

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
  {V ι : Type} [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.PrismTransfer
theorem _root_.solution {n : ℕ} (b : Basis ι K V) (c : K) (x : Fin n → V →ₗ[K] V) (k : ι)
    (i : Fin n) (j : ι) :
    LinearMap.toMatrix b (Pi.basis fun _ : Fin n => b) (colMap c x) ⟨i, j⟩ k =
      c * LinearMap.toMatrix b b (x i) j k := by
  simp [LinearMap.toMatrix_apply, Pi.basis_repr, colMap_apply]
end Formalism.BranchingDeterminantCap.PrismTransfer
