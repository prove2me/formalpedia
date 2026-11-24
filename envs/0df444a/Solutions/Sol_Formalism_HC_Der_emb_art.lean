-- Prove2me | solution 1 for Formalism.HC.Der.emb_art
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T20:17:54.973005+00:00
-- url     : https://prove2.me/submissions/63cfbd78-0323-4f06-8390-8892be83b5b2

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_DecompTypeI
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_CycBasic
import Theorems.Thm_Formalism_HC_Der_tauN_root
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
theorem _root_.solution (u : (ZMod H.condN)ˣ) (x : H.E) :
    emb H (H.gal.symm (H.art u) x) = tauN H.condN u (emb H x) :=
  H.art_spec u (tauN H.condN u) (tauN_root H.condN u _ H.cycZeta_prim.pow_eq_one) x
end Formalism.HC.Der
