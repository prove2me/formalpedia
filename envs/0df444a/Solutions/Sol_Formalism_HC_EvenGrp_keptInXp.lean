-- Prove2me | solution 1 for Formalism.HC.EvenGrp.keptInXp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T16:55:09.523505+00:00
-- url     : https://prove2.me/submissions/c961f802-efd1-4225-99af-6a10458bfc6e

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenGrp_exact
import Theorems.Thm_Formalism_HC_EvenGrp_keptEqChat
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_HC_EvenData_exact
import Theorems.Thm_Formalism_HC_Frame_iotaInv_iota
import Theorems.Thm_Formalism_HC_Frame_iota_iotaInv
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.HC.Frame.iotaInv_iota
attribute [local simp] Formalism.HC.Frame.iota_iotaInv



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
theorem _root_.solution : (host Ξ e hev hH hc he hs).KeptInXp (Level.ofSub Ξ).KEPT := by
  have hk := keptEqChat Ξ e hev hH hc he hs
  unfold HostRaw.KeptEqChat at hk
  unfold HostRaw.KeptInXp
  intro ψ hψ
  obtain ⟨θ, hθ, h⟩ := hk.1 ψ hψ
  refine ⟨θ, ?_, h⟩
  simp only [Frame.Chat, Frame.Xp, Set.mem_setOf_eq] at hθ ⊢
  exact ⟨hθ.1, hθ.2.1⟩
end Formalism.HC.EvenGrp
