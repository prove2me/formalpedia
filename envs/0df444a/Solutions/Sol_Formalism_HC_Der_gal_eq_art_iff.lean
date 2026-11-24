-- Prove2me | solution 1 for Formalism.HC.Der.gal_eq_art_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:34:13.877306+00:00
-- url     : https://prove2.me/submissions/12312f66-6592-49f0-8066-8c445b608da6

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_emb_art
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb


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
variable {φ : Frame} (H : HostRaw φ)
namespace Formalism.HC.Der
theorem _root_.solution (σ : H.E ≃ₐ[ℚ] H.E) (u : (ZMod H.condN)ˣ) :
    H.gal σ = H.art u ↔ ∀ x, emb H (σ x) = tauN H.condN u (emb H x) := by
  constructor
  · intro h x
    rw [← emb_art, ← h, MulEquiv.symm_apply_apply]
  · intro h
    have h1 : σ = H.gal.symm (H.art u) :=
      AlgEquiv.ext fun x => (emb H).injective (by show emb H _ = emb H _; rw [h, emb_art])
    rw [h1, MulEquiv.apply_symm_apply]
end Formalism.HC.Der
