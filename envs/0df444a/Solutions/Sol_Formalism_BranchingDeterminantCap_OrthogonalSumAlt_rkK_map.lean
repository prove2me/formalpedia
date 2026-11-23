-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.rkK_map
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T10:22:21.449945+00:00
-- url     : https://prove2.me/submissions/61ed6557-5897-4493-85a4-40ccd05b0c07

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
theorem _root_.solution {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W]
    [IsScalarTower (𝓞 K) K W] (ψ : V →ₗ[K] W) (hψ : Function.Injective ψ)
    (A : Submodule (𝓞 K) V) :
    Formalism.HN.rkK (A.map (ψ.restrictScalars (𝓞 K))) = Formalism.HN.rkK A := by
  unfold Formalism.HN.rkK
  have h : Submodule.span K ((A.map (ψ.restrictScalars (𝓞 K)) : Submodule (𝓞 K) W) : Set W) =
      (Submodule.span K (A : Set V)).map ψ := by
    rw [Submodule.map_span]
    rfl
  rw [h]
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective ψ hψ _)).symm
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
