-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.blockInv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:13.419968+00:00
-- url     : https://prove2.me/submissions/4964f7c6-a838-4f45-8394-bd41c6fa21d7

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum

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
open Formalism.BranchingDeterminantCap.OrthogonalSumAlt
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.BranchingDeterminantCap.OrthogonalSumAlt
theorem _root_.solution (X : InfinitePlace K → Matrix ι ι ℂ) (hX : ∀ v, IsUnit (X v).det) (n : ℕ)
    (v : InfinitePlace K) :
    (Matrix.blockDiagonal' fun _ : Fin n => X v) * (Matrix.blockDiagonal' fun _ : Fin n => (X v)⁻¹)
      = 1 := by
  rw [← Matrix.blockDiagonal'_mul]
  simp only [Matrix.mul_nonsing_inv _ (hX v)]
  exact Matrix.blockDiagonal'_one
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
