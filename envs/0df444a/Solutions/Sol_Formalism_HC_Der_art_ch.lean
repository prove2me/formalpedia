-- Prove2me | solution 1 for Formalism.HC.Der.art_ch
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T20:34:19.238097+00:00
-- url     : https://prove2.me/submissions/92902f5b-7b88-40c6-96f7-cc34a67e4f3c

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_tauN_root
import Theorems.Thm_Formalism_HC_Der_emb_art
import Theorems.Thm_Formalism_HC_Der_sqd_ne_zero
import Theorems.Thm_Formalism_HC_Der_d_mod_four
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_emb
import Theorems.Thm_Formalism_HC_HostAx_sqd_ne_zero


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
theorem _root_.solution : ∀ u : (ZMod H.condN)ˣ,
    (((H.art u).1.2 : ℤˣ) : ℤ) = jacobiSym (((u : ZMod H.condN).val : ℕ) : ℤ) H.d := by
  intro u
  have hd : H.d ∣ H.condN := dvd_mul_left _ _
  have h1 := D7.sqrt_act H.hyp.2.1 (d_mod_four H) hd u (tauN H.condN u) (tauN_root H.condN u) (emb H H.sqd)
    (by rw [← map_pow, H.sqd_sq, map_neg, map_natCast])
  rw [← emb_art, H.gal_sqd, MulEquiv.apply_symm_apply, map_mul, map_intCast, D7.sgnN_val] at h1
  have h2 := mul_right_cancel₀ ((map_ne_zero (emb H)).mpr (sqd_ne_zero H)) h1
  exact_mod_cast h2
end Formalism.HC.Der
