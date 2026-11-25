-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.GC.smooth_K_finite_form_one_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T16:49:59.79553+00:00
-- url     : https://prove2.me/submissions/fa4e1427-c9c4-4cfd-b628-8916b00eb0c2

import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtFormAdmOneOfSteps
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_DiscreteSeriesFormOneReduction
import Definitions.Def_CompanionTheory_HarishChandraModules_BesselParameterIntegrals_BesselOrbitConvolutions_AtFormC
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_ae_UH_of_quot
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_bessel_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_fdeg_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_l2_norm_scaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_muSof_facts
import Theorems.Thm_PI_UnitaryGroupMassFormula_CapelliEig_smooth_right_action


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate
noncomputable section
set_option maxHeartbeats 1600000
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.DDSmoothness
open Formalism.FourierDecayAlt.ThreeDimData
open Formalism.FourierDecayAlt.P.DDSmoothness.GC
namespace Formalism.FourierDecayAlt.P.DDSmoothness.GC
theorem _root_.solution : CompanionTheory.D.Upq.BesselFunctionalConstruction.C.AtFormOneOfSteps := by
  intro hSch hBC hNI hBB hSh hKF hZ hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => fdeg_eq hd hSd hx
  have hmu := muSof_facts hW hN
  have hae := ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  have hKs : ∀ v : H, PI.UpqRep.IsKFinHpk (k := k) (r := r) σ v →
      v ∈ PI.UpqRep.smoothVecs (k := k) (r := r) σ := fun v hv => hIn.2.2.1 k r ε lam H σ hlam hσ v hv
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, hx1, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    have hK := hKF hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS l hl hx1 hid
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x hx v (Or.inr hv), hK v hv x hx⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x hx v (Or.inr hv) (l v)).1
    rw [hK v hv v (hKs v hv)] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hK v hv _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x hx _ hg)]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    have h0 := hZ hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x hx v (Or.inr hv), ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    rw [h0 v hv x hx]
    ext ξ; simp
end Formalism.FourierDecayAlt.P.DDSmoothness.GC
