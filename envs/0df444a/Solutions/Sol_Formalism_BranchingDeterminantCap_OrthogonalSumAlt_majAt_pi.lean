-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_pi
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:20.584444+00:00
-- url     : https://prove2.me/submissions/4540374c-2f4b-48da-9ad7-b22195a7d0bb

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_BranchingDeterminantCap_OrthogonalSumAlt_fcoord_pi

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) (n : ℕ) (v : InfinitePlace K) (x y : Fin n → V) :
    Formalism.HermitianLatticesTheory.majAt (Pi.basis fun _ : Fin n => b)
      (fun v => Matrix.blockDiagonal' fun _ : Fin n => X v) v x y =
        ∑ j, Formalism.HermitianLatticesTheory.majAt b X v (x j) (y j) := by
  simp only [Formalism.HermitianLatticesTheory.majAt, Fintype.sum_sigma, fcoord_pi b X hX]
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
