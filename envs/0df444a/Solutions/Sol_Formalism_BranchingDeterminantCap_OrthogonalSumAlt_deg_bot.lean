-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.deg_bot
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T03:53:18.32501+00:00
-- url     : https://prove2.me/submissions/59992c73-b97a-4fc4-acfc-15eb463f2409

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_HN_hnSum
import Theorems.Thm_Formalism_HN_plLat


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
    (hX : ∀ v, IsUnit (X v).det) :
    Formalism.HN.deg (Formalism.HermitianLatticesTheory.realize b X) (⊥ : Submodule (𝓞 K) V) = 0 := by
  have hl := (Formalism.HN.plLat K V ι b X hX ⊥ Submodule.fg_bot).1
  have h := ((Formalism.HN.hnSum.{0, 0, 0, 0} (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X)).2 ⊥ ⊥ hl hl (by
    intro x hx y hy
    rw [(Submodule.mem_bot _).1 hx]
    simp)).2.1
  rw [sup_idem] at h
  linarith
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
