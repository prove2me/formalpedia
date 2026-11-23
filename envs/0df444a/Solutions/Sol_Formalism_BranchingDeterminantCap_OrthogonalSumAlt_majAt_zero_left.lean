-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.majAt_zero_left
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:20.755628+00:00
-- url     : https://prove2.me/submissions/7cfd807d-02aa-4152-a1e7-99a8dad0ce0a

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
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (v : InfinitePlace K) (y : V) : Formalism.HermitianLatticesTheory.majAt b X v 0 y = 0 := by
  simp [Formalism.HermitianLatticesTheory.majAt, Formalism.HermitianLatticesTheory.fcoord_zero]
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
