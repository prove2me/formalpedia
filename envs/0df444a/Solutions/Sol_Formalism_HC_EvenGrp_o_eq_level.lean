-- Prove2me | solution 1 for Formalism.HC.EvenGrp.o_eq_level
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:13:35.097764+00:00
-- url     : https://prove2.me/submissions/faa88334-f60c-4b34-8bad-460845a067c0

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenGrp_o_eq
import Theorems.Thm_Formalism_HC_EvenData_o_eq


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
variable {q d : ℕ} (hH : HostHyp q d) (hc : Nat.Coprime M (q * d)) (he : 2 ≤ e)
  (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ M → jacobiSym (-(d : ℤ)) l = 1)
namespace Formalism.HC.EvenGrp
theorem _root_.solution : (frame Ξ e hev).o = (Level.ofSub Ξ).o := o_eq Ξ e hev
end Formalism.HC.EvenGrp
