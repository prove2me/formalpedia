-- Prove2me | solution 1 for Formalism.HC.Der.art_surj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:51:56.878813+00:00
-- url     : https://prove2.me/submissions/117d7094-8668-4ec3-ad32-31d36ae3af41

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_exists_lift
import Theorems.Thm_Formalism_HC_Der_cyc_isGalois
import Theorems.Thm_Formalism_HC_Der_gal_eq_art_iff
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Galois_exists_lift


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
theorem _root_.solution : Function.Surjective H.art := by
  intro g
  have := cyc_isGalois H.condN
  obtain ⟨τ, hτ⟩ := exists_lift (emb H) (H.gal.symm g)
  obtain ⟨u, rfl⟩ := (tauN H.condN).surjective τ
  exact ⟨u, by rw [← (gal_eq_art_iff H _ u).mpr hτ, MulEquiv.apply_symm_apply]⟩
end Formalism.HC.Der
