-- Prove2me | solution 1 for Formalism.HC.EvenGrp.psQ
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:04:09.521845+00:00
-- url     : https://prove2.me/submissions/3a84d69b-3f3f-4ae8-9528-71932fa6b267

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenData_psQ


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
theorem _root_.solution : (host Ξ e hev hH hc he hs).PsQ := by
  apply (data Ξ e hev).psQ
end Formalism.HC.EvenGrp
