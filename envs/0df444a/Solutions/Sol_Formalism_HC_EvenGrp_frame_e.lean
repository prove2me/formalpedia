-- Prove2me | solution 1 for Formalism.HC.EvenGrp.frame_e
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:53:11.839719+00:00
-- url     : https://prove2.me/submissions/73a04d11-fcdb-4094-acb8-7fefba1bce3a

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.HC
open Formalism.FrobeniusOrbits
open Formalism.HC.EvenGrp
variable {M : ℕ} [NeZero M] (Ξ : Subgroup (DirichletCharacter ℂ M)) (e : ℕ)
variable (hev : ∀ χ ∈ Ξ, χ.Even)
namespace Formalism.HC.EvenGrp
theorem _root_.solution : (frame Ξ e hev).e = e := rfl
end Formalism.HC.EvenGrp
