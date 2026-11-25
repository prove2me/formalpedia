-- Prove2me | solution 1 for Formalism.BranchingDeterminantCap.OrthogonalSumAlt.muMax_mono
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:29:26.711902+00:00
-- url     : https://prove2.me/submissions/ce7c14f9-24e4-43d9-8d7a-c1ed9ccc6a48

import Definitions.Def_Formalism_BranchSandwichDivisors_StatementL
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_MapScale
import Definitions.Def_Formalism_BranchSandwichDivisors_BranchIsometryProofs_OrthSum
import Theorems.Thm_Formalism_HN_muChar
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
    (hX : ∀ v, IsUnit (X v).det) {N L : Submodule (𝓞 K) V} (hN : N.FG) (hL : L.FG) (hNL : N ≤ L)
    (h0 : N ≠ ⊥) :
    Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) N ≤ Formalism.HN.muMax (Formalism.HermitianLatticesTheory.realize b X) L := by
  have hL0 : L ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hNL))
  have h1 := (Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) N
    (Formalism.HN.plLat K V ι b X hX N hN).1 h0).1
  have h2 := (Formalism.HN.muChar (𝓞 K) V _ (Formalism.HermitianLatticesTheory.realize b X) L
    (Formalism.HN.plLat K V ι b X hX L hL).1 hL0).1
  exact (h1 _).2 fun M hM => (h2 _).1 le_rfl M (hM.trans hNL)
end Formalism.BranchingDeterminantCap.OrthogonalSumAlt
