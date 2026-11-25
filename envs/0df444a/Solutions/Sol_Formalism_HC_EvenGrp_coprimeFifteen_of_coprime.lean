-- Prove2me | solution 1 for Formalism.HC.EvenGrp.coprimeFifteen_of_coprime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:00:17.818727+00:00
-- url     : https://prove2.me/submissions/34d4f328-9b1d-4c78-a05e-ffeb47655adc

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenGrp_exact
import Theorems.Thm_Formalism_HC_EvenData_exact


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
theorem _root_.solution (h : Nat.Coprime M 15) : (host Ξ e hev hH hc he hs).CoprimeFifteen := by
  show Nat.Coprime (QS Ξ e) 15
  exact Nat.Coprime.coprime_dvd_left (QS_dvd_mul Ξ e) (Nat.Coprime.mul (Nat.Coprime.pow_left _ (by decide)) h)
end Formalism.HC.EvenGrp
