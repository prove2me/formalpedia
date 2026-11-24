-- Prove2me | solution 1 for CompanionTheory.D.DSIC.algCore_of
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:48:28.551115+00:00
-- url     : https://prove2.me/submissions/fb0406e8-c96f-4379-ac24-910fd64effd8

import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CapelliDeterminantBlockProduct
import Definitions.Def_Formalism_RealPlaceAnalysis_ThirdArithmeticHolds
import Definitions.Def_CompanionTheory_HarishChandraModules_LowKTypeMultiplicity_DiscreteSeriesCharacters_CobApplyOfDeg
import Theorems.Thm_CompanionTheory_D_DSIC_lift_Gop
import Theorems.Thm_CompanionTheory_D_DSIC_kHighest_map
import Theorems.Thm_CompanionTheory_D_DSIC_bd_apply_of_deg
import Theorems.Thm_CompanionTheory_D_DSIC_cob_apply_of_deg
import Theorems.Thm_CompanionTheory_D_DSIC_lift_apply
import Theorems.Thm_Formalism_REAL_qDetCentral
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] CompanionTheory.D.DSIC.lift_apply



set_option autoImplicit false
open Matrix Finset
open scoped InnerProductSpace
noncomputable section
open CompanionTheory CompanionTheory.D CompanionTheory.D.DSIC
open Formalism.REAL (GlRel IsUnitary KHighest IsWeight qdet qminor)
open PI.UpqRep (lowK vNormSq IsHCParam IsURepOn IsIrredOn UJset Kset IsKFin IsKTypeOf IsWtOn inG inK IsKStableOn)
variable {n : ℕ} {ε : Fin n → Bool}
namespace CompanionTheory.D.DSIC
theorem _root_.solution (hF : FRel) (hB : BdFacts) (hCO : CO) (hZ : ZetaHW) (hW : WLem) (hN : NormLt) (hA : Adj)
    (hP : PRV) : AlgCore := by
  intro n ε lam V _ _ E v S hlam hgl hu hv hS hSt hvS hmin Y
  have hK : KRel ε E := fun a b c d _ _ => hgl a b c d
  have hKU : KUnit ε E := fun a b h x y => by rw [hu a b x y]; simp [Formalism.REAL.sgn, h]
  obtain ⟨c, hcd, hc, hcv⟩ := hP n ε lam V E v S hlam hK hKU hv hS hSt hvS
  have van : ∀ y : Ch ε V, KHighest ε (Fop ε E) (gam ε lam) y → y (A1 ε) = 0 → y = 0 := by
    intro y hy h0
    by_contra hne
    obtain ⟨A, hA0, hAh⟩ := hW n ε V E _ y hne hy
    have hA1 : A ≠ A1 ε := fun h => hA0 (h ▸ h0)
    exact absurd (hmin _ _ hA0 hAh) (not_le.2 (hN n ε lam hlam.1 A hA1))
  obtain ⟨-, hcomm⟩ := hB n ε V E hgl
  have hbd : bd ε E c = 0 :=
    van _ (kHighest_map hc fun a b h => (hcomm a b h).1) (bd_apply_of_deg E hcd rfl)
  set u : ℂ := Y + ((n : ℂ) - 1) / 2
  set s : ℂ := Formalism.QuantumDeterminants.capP (fun s => (lam s : ℂ)) Y
  obtain ⟨w, -, hw⟩ := hCO n ε V E hgl u _ c hcd hbd
  rw [hZ n ε lam _ _ c (hF n ε V E hK).1 hc Y] at hw
  let T : Module.End ℂ (Ch ε V) := lift ε (qdet E u - s • 1)
  have hT : T c = bd ε E w := by
    rw [← hw]; funext A; simp [T, s]
  have hTc : ∀ a b, ε a = ε b → Commute (Fop ε E a b) T := by
    intro a b _
    refine Commute.add_left ?_ (lift_Gop _ a b).symm
    refine LinearMap.ext fun x => funext fun A => ?_
    have := congrArg (fun S : Module.End ℂ V => S (x A)) (Formalism.REAL.qDetCentral _ n E hgl u a b)
    simp only [Module.End.mul_apply] at this
    simp [T, this]
  have hx := kHighest_map hc hTc
  have hxd : Deg (A1 ε).card (T c) := fun A hA => by simp [T, hcd A hA]
  have hcob : cob ε E (T c) = 0 :=
    van _ (kHighest_map hx fun a b h => (hcomm a b h).2) (cob_apply_of_deg E hxd rfl)
  have h0 : ip (T c) (T c) = 0 := by
    conv_lhs => enter [1]; rw [hT]
    rw [hA n ε V E hu, hcob]; simp [ip]
  have h1 : (∑ A, ‖T c A‖ ^ 2 : ℝ) = 0 := by
    have h := congrArg (RCLike.re (K := ℂ)) h0
    simp only [ip, map_sum, inner_self_eq_norm_sq, map_zero] at h
    exact h
  have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun A _ => sq_nonneg _).1 h1 (A1 ε) (Finset.mem_univ _)
  have h3 : T c (A1 ε) = 0 := by simpa using h2
  simpa [T, hcv, sub_eq_zero] using h3
end CompanionTheory.D.DSIC
