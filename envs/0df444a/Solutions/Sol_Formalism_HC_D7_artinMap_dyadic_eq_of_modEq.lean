-- Prove2me | solution 1 for Formalism.HC.D7.artinMap_dyadic_eq_of_modEq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T19:43:42.839545+00:00
-- url     : https://prove2.me/submissions/4315817f-aeb0-4c9d-81f9-c5a5cb119982

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSym
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Theorems.Thm_Formalism_FrobeniusOrbits_Cond_two_dvd


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC Formalism.HC.D7
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {q d : ℕ} (e : ℕ) (hH : HostHyp q d)
include hH
namespace Formalism.HC.D7
theorem _root_.solution (u : (ZMod (2 ^ (e + 2) * q * d))ˣ) {y : ℕ}
    (hu : (u : ZMod (2 ^ (e + 2) * q * d)).val ≡ y [MOD 2 ^ (e + 2)]) (v : (ZMod (2 ^ (e + 2)))ˣ)
    (hv : (v : ZMod (2 ^ (e + 2))) = (y : ZMod (2 ^ (e + 2)))) : (art0 e hH u).2 = hcl e v := by
  haveI := neZeroN e hH
  have h1 : ZMod.unitsMap (two_dvd e q d) u = v := by
    apply Units.ext
    rw [hv]
    change ZMod.cast (u : ZMod (2 ^ (e + 2) * q * d)) = _
    rw [← ZMod.natCast_zmod_val (u : ZMod (2 ^ (e + 2) * q * d)), ZMod.cast_natCast (two_dvd e q d)]
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr hu
  have h2 : (art0 e hH u).2 = QuotientGroup.mk (ZMod.unitsMap (two_dvd e q d) u) := rfl
  rw [h2, h1]
  rfl
end Formalism.HC.D7
