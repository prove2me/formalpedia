-- Prove2me | solution 1 for Formalism.HC.Der.cmType_iff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T21:19:39.940911+00:00
-- url     : https://prove2.me/submissions/8dc802e0-beeb-4356-8b49-da4cf13f13be

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycGrp
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycAll
import Theorems.Thm_Formalism_HC_Der_I_sqrt_ne_zero
import Theorems.Thm_Formalism_HC_Der_emb_sqd
import Theorems.Thm_Formalism_FrobeniusOrbits_Final_cmType
import Theorems.Thm_Formalism_HC_Der_conj_apply
import Theorems.Thm_Formalism_HC_Der_conj_sqd


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
theorem _root_.solution (ψ : H.E →+* ℂ) : ψ ∈ H.cmType ↔ (starRingEnd ℂ).comp ψ ∉ H.cmType := by
  have h0 := I_sqrt_ne_zero H
  show ψ H.sqd = _ ↔ ¬ starRingEnd ℂ (ψ H.sqd) = _
  rw [← conj_apply, conj_sqd, map_neg]
  constructor
  · intro h1 h2
    apply h0
    linear_combination (-1 / 2 : ℂ) * h1 + (-1 / 2 : ℂ) * h2
  · intro h1
    exact (emb_sqd H ψ).resolve_right fun h2 => h1 (by rw [h2, neg_neg])
end Formalism.HC.Der
