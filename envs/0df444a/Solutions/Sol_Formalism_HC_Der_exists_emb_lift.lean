-- Prove2me | solution 1 for Formalism.HC.Der.exists_emb_lift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T19:56:34.306225+00:00
-- url     : https://prove2.me/submissions/4fae6bbc-ccf8-464f-98ac-0916457109af

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
theorem _root_.solution (ι : E →ₐ[ℚ] L) (ψ : E →+* ℂ) : ∃ Ψ : L →+* ℂ, ∀ x, Ψ (ι x) = ψ x := by
  let _ : Algebra E L := ι.toRingHom.toAlgebra
  have : IsScalarTower ℚ E L := IsScalarTower.of_algebraMap_eq fun x => (ι.commutes x).symm
  have : Algebra.IsAlgebraic E L := Algebra.IsAlgebraic.tower_top (K := ℚ) E
  exact ⟨ComplexEmbedding.lift L ψ, fun x => ComplexEmbedding.lift_algebraMap_apply L ψ x⟩
end Formalism.HC.Der
