-- Prove2me | solution 1 for Formalism.HC.EvenGrp.exists_theta
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:45:05.708795+00:00
-- url     : https://prove2.me/submissions/96cfe3ce-5999-4867-ad1c-b252287696c5

import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharFrame
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_ExplicitFormulaErrorOfHostConditions
import Definitions.Def_Formalism_SharpRestriction_RamificationFrobenius_TotientGaloisClasses_InertiaGaloisSymmetry_OfCharLevel
import Theorems.Thm_Formalism_HC_EvenGrp_mem_iff
import Theorems.Thm_Formalism_HC_EvenGrp_xi_surj
import Theorems.Thm_Formalism_HC_EvenGrp_theta_toA
import Theorems.Thm_Formalism_HC_EvenData_exact
import Theorems.Thm_Formalism_HC_EvenData_mem_cusp_forms_iff_automorphic_compact
import Theorems.Thm_Formalism_HC_EvenData_xiA_toA
import Theorems.Thm_Formalism_HC_Frame_cc_mul_iod
import Theorems.Thm_Formalism_HC_Frame_mem_cusp_forms_iff_automorphic_compact


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
theorem _root_.solution (θ : (frame Ξ e hev).Char) (hθ : θ ∈ (frame Ξ e hev).Chat) : ∃ χ hχ, theta Ξ e hev χ hχ = θ := by
  obtain ⟨h1, h2, h3⟩ := hθ
  set D := data Ξ e hev with hD
  have hsurj : Function.Surjective D.xiA := fun b => by
    obtain ⟨u, rfl⟩ := xi_surj Ξ e b
    exact ⟨D.toA u, D.xiA_toA u⟩
  let θA : D.frame.MA →* ℂˣ := θ.comp (MonoidHom.inr G0 D.frame.MA)
  let θB : B Ξ →* ℂˣ := D.xiA.liftOfSurjective hsurj ⟨θA, fun a ha => h1 a.toAdd ((D.mem_cusp_forms_iff_automorphic_compact a.toAdd).mpr ha)⟩
  have hB : ∀ a, θB (D.xiA a) = θA a := fun a => MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ a
  have hχ : MulChar.ofUnitHom (θB.comp (QuotientGroup.mk' _)) ∈ Ξ := by
    refine (mem_iff Ξ _).mpr fun u hu => ?_
    rw [MulChar.ofUnitHom_coe, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff u).mpr hu, map_one,
      Units.val_one]
  have h0 : ∀ s : G0, θ (s, 1) = 1 := by
    rintro ⟨s, t⟩
    have h4 : θ (frame Ξ e hev).sg = 1 := by rw [← Frame.cc_mul_iod, map_mul, h2, h3, one_mul]
    rcases Int.units_eq_one_or s with rfl | rfl <;> rcases Int.units_eq_one_or t with rfl | rfl
    · exact map_one θ
    · exact h2
    · exact h4
    · exact h3
  refine ⟨_, hχ, MonoidHom.ext fun g => ?_⟩
  obtain ⟨s, a⟩ := g
  obtain ⟨v, rfl⟩ := D.toA_surj a
  obtain ⟨u, rfl⟩ := ZMod.unitsMap_surjective (QS_dvd Ξ e) v
  refine (theta_toA Ξ e hev _ hχ s u).trans (Units.ext ?_)
  have h5 : θ (s, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) = θA (D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) := by
    have h6 : ((s, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) : (frame Ξ e hev).GG) =
        (s, 1) * (1, D.toA (ZMod.unitsMap (QS_dvd Ξ e) u)) := Prod.ext (mul_one _).symm (one_mul _).symm
    exact (congrArg θ h6).trans ((map_mul θ _ _).trans ((congrArg (· * _) (h0 s)).trans (one_mul _)))
  rw [MulChar.coe_toUnitHom, MulChar.ofUnitHom_coe]
  refine congrArg Units.val (Eq.trans ?_ h5.symm)
  exact (congrArg θB ((D.xiA_toA _).trans (xi_unitsMap Ξ e u))).symm.trans (hB _)
end Formalism.HC.EvenGrp
