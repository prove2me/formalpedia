-- Prove2me | solution 1 for Formalism.HC.Der.exists_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T19:57:45.800495+00:00
-- url     : https://prove2.me/submissions/9112d66d-5621-4900-813f-661e2bcb8faf

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.HC Formalism.HC.Der
open Formalism.FrobeniusOrbits
variable {E L : Type} [Field E] [NumberField E] [Field L] [NumberField L]
namespace Formalism.HC.Der
theorem _root_.solution [IsGalois ℚ L] (ι : E →ₐ[ℚ] L) (σ : E ≃ₐ[ℚ] E) :
    ∃ τ : L ≃ₐ[ℚ] L, ∀ x, ι (σ x) = τ (ι x) := by
  let _ : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  exact ⟨σ.liftNormal L, fun x => (AlgEquiv.liftNormal_commutes σ L x).symm⟩
end Formalism.HC.Der
