-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.eq_bot_of_rkK
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T23:21:13.402688+00:00
-- url     : https://prove2.me/submissions/96857927-407b-4c44-9645-157d424beed6

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
theorem _root_.solution (b : Basis ι K V) {L : Submodule (𝓞 K) V} (h : Formalism.HN.rkK L = 0) :
    L = ⊥ := by
  have : Module.Finite K V := Module.Finite.of_basis b
  have h1 : Submodule.span K (L : Set V) = ⊥ := Submodule.finrank_eq_zero.1 h
  rw [Submodule.span_eq_bot] at h1
  exact (Submodule.eq_bot_iff _).2 fun x hx => h1 x hx
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
