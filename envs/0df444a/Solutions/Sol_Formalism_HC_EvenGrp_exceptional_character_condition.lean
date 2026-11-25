-- Prove2me | solution 1 for Formalism.HC.EvenGrp.exceptional_character_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T17:02:14.073401+00:00
-- url     : https://prove2.me/submissions/d5c74157-5b13-4b6d-a675-0c1f74f6c269

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_HostRaw_art_eq_of_prim_eq
import Theorems.Thm_Formalism_HC_EvenGrp_theta_mem
import Theorems.Thm_Formalism_HC_EvenGrp_prim_theta
import Theorems.Thm_Formalism_FrobeniusOrbits_Eta_cases
import Theorems.Thm_Formalism_HC_HostRaw_kept_iff
import Theorems.Thm_Formalism_HC_Level_mem_ofSub


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
theorem _root_.solution : (host Ξ e hev hH hc he hs).ExceptionalCharacterKept (Level.ofSub Ξ).KEPT (Level.ofSub Ξ).psK := by
  refine ⟨fun ψ h => (by cases h), fun _ h => ?_⟩
  obtain ⟨χ, hχ, h1⟩ := (Level.mem_ofSub Ξ _).mp ((HostRaw.kept_iff _ _ _).mp h)
  rw [prim_theta Ξ e hev hH hc he hs χ hχ] at h1
  have h2 := HostRaw.art_eq_of_prim_eq _ h1 (-1)
  rw [HostRaw.art_neg_one, (theta_mem Ξ e hev χ hχ).2.2] at h2
  have h3 : (1 : ℂ) = ((-1 : ℤ) : ℂ) := congrArg Units.val h2
  norm_num at h3
end Formalism.HC.EvenGrp
