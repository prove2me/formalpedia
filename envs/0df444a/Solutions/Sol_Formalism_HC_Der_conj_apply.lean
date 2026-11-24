-- Prove2me | solution 1 for Formalism.HC.Der.conj_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:51:59.274806+00:00
-- url     : https://prove2.me/submissions/bbaf1c86-4992-4752-9f4e-56268fb434a3

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_exists_emb_lift
import Theorems.Thm_Formalism_HC_Der_tauN_neg_one
import Theorems.Thm_Formalism_HC_Der_gal_eq_art_iff
import Theorems.Thm_Formalism_HC_Der_gal_conj
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_conj


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
theorem _root_.solution (ψ : H.E →+* ℂ) (x : H.E) : ψ (H.conj x) = starRingEnd ℂ (ψ x) := by
  obtain ⟨Ψ, hΨ⟩ := exists_emb_lift (emb H) ψ
  rw [← hΨ, ← hΨ, ← tauN_neg_one, (gal_eq_art_iff H H.conj (-1)).mp ((gal_conj H).trans H.art_neg_one.symm)]
end Formalism.HC.Der
