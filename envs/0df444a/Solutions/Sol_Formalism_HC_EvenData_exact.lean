-- Prove2me | solution 1 for Formalism.HC.EvenData.exact
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T20:33:50.295897+00:00
-- url     : https://prove2.me/submissions/354bbe09-8efb-4367-b524-40d28d696011

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfChar
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ArtinMapSecondEqJacobiSymOfModEq
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_FrameFacts
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Theorems.Thm_Formalism_HC_D7_cop_qd


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
attribute [instance] EvenData.grp
open Formalism.HC.EvenData
variable (D : EvenData)
variable {q d : ℕ} (hH : HostHyp q d)
variable (hc : Nat.Coprime D.m (q * d))
variable (he : 2 ≤ D.e) (hs : ∀ l : ℕ, l.Prime → l ≠ 2 → l ∣ D.m → jacobiSym (-(d : ℤ)) l = 1)
namespace Formalism.HC.EvenData
theorem _root_.solution (h : ∀ l : ℕ, l.Prime → l ∣ D.m → ∃ v : (ZMod D.m)ˣ, (v : ZMod D.m).val ≡ 1 [MOD D.m / l] ∧ D.eta v ≠ 1) :
    (D.host hH hc he hs).Exact := by
  have := D.neZeroN hH
  intro l hl (hlm : l ∣ D.m)
  obtain ⟨v, hv, hv1⟩ := h l hl hlm
  obtain ⟨u, h1, h2, h3⟩ := exists_unit_three hc.coprime_mul_right_right hc.coprime_mul_left_right (D7.cop_qd hH)
    (v : ZMod D.m).val 1 1 (ZMod.val_coe_unit_coprime v) (Nat.coprime_one_left _) (Nat.coprime_one_left _)
  refine ⟨u, ?_, fun h4 => hv1 ?_⟩
  · show (u : ZMod (D.m * q * d)).val ≡ 1 [MOD D.m * q * d / l]
    have h5 : D.m * q * d / l = D.m / l * (q * d) := by rw [mul_assoc, Nat.div_mul_right_comm hlm]
    have h6 : D.m / l ∣ D.m := Nat.div_dvd_of_dvd hlm
    rw [h5]
    exact (Nat.modEq_and_modEq_iff_modEq_mul (hc.coprime_dvd_left h6)).mp
      ⟨(h1.of_dvd h6).trans hv, (Nat.modEq_and_modEq_iff_modEq_mul (D7.cop_qd hH)).mp ⟨h2, h3⟩⟩
  · have h5 : (D.art hH u).2 = 1 := congrArg Prod.snd h4
    rw [art_snd, (unitsMap_eq_iff _ u v).mpr h1] at h5
    exact (D.toA_eq_one_iff v).mp h5
end Formalism.HC.EvenData
