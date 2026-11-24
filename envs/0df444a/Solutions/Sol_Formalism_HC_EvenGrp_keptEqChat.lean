-- Prove2me | solution 1 for Formalism.HC.EvenGrp.keptEqChat
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T22:15:47.50225+00:00
-- url     : https://prove2.me/submissions/57329d4d-5ec1-44ce-9e4a-fd647e634680

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenGrp_theta_mem
import Theorems.Thm_Formalism_HC_EvenGrp_exists_theta
import Theorems.Thm_Formalism_HC_EvenGrp_exact
import Theorems.Thm_Formalism_HC_EvenGrp_prim_theta
import Theorems.Thm_Formalism_HC_EvenData_exact
import Theorems.Thm_Formalism_HC_HostRaw_isPrimOf_iff
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
theorem _root_.solution : (host Ξ e hev hH hc he hs).KeptEqChat (Level.ofSub Ξ).KEPT := by
  unfold HostRaw.KeptEqChat HostRaw.Kept
  refine ⟨fun ψ hψ => ?_, fun θ hθ => ?_⟩
  · obtain ⟨χ, hχ, rfl⟩ := (Level.mem_ofSub Ξ ψ).mp hψ
    exact ⟨theta Ξ e hev χ hχ, theta_mem Ξ e hev χ hχ,
      ((host Ξ e hev hH hc he hs).isPrimOf_iff _ _).mpr (prim_theta Ξ e hev hH hc he hs χ hχ)⟩
  · obtain ⟨χ, hχ, rfl⟩ := exists_theta Ξ e hev θ hθ
    exact ⟨PChar.of χ, (Level.mem_ofSub Ξ _).mpr ⟨χ, hχ, rfl⟩,
      ((host Ξ e hev hH hc he hs).isPrimOf_iff _ _).mpr (prim_theta Ξ e hev hH hc he hs χ hχ)⟩
end Formalism.HC.EvenGrp
