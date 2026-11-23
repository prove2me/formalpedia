-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.orth_inner
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:21.256969+00:00
-- url     : https://prove2.me/submissions/be3ef526-fcd7-43d5-9299-87d808b14fa6

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_HN_HeightGram_inner_realize


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
    {A B : Submodule (𝓞 K) V} (h : OrthAt b X A B) :
    ∀ x ∈ A, ∀ y ∈ B, inner ℝ (Formalism.HermitianLatticesTheory.realize b X x) (Formalism.HermitianLatticesTheory.realize b X y) = 0 := by
  intro x hx y hy
  rw [Formalism.HN.HeightGram.inner_realize]
  exact Finset.sum_eq_zero fun v _ => by rw [h v x hx y hy]; simp
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
