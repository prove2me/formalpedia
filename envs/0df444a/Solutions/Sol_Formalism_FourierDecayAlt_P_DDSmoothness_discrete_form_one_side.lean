-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.DDSmoothness.discrete_form_one_side
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:28:35.674323+00:00
-- url     : https://prove2.me/submissions/2efe2f44-6a53-4ceb-af6d-376414416f54

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_UhMeasurableSet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_L2NormScaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_l2_norm_scaling
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_DD_smooth
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_ae_UH_of_quot
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_bessel_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_DDSmoothness_fdeg_eq
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
namespace Formalism.FourierDecayAlt.P.DDSmoothness
theorem _root_.solution : DDFormOneOfSteps := by
  intro hPsi hSch _ _ _ _ hBC hNI hBB hSh hIn k r ε lam h H _ _ _ σ w0 Wp _ _ _ _ z c u π μW μN μG νq hS
  have hS' := hS
  obtain ⟨hlam, hσ, -, -, hw0, -, -, -, -, hW, hN, hG, hq⟩ := hS'
  have hsm := DD_smooth hIn.2.2.1 hlam hσ hw0
  obtain ⟨hBC1, -, -, -⟩ := hBC hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS
  obtain ⟨d, hd, hSd⟩ := hSch k r ε lam H σ μG hlam hσ hG
  have hw0n : w0 ≠ 0 := by
    obtain ⟨P, -, hn1, -⟩ := hw0
    intro h0; rw [h0, norm_zero] at hn1; exact zero_ne_one hn1
  have hdeg : ∀ x : H, x ≠ 0 → PI.BesselPeriodGGP.fdegH μG σ x = d := fun x hx => fdeg_eq hd hSd hx
  have hmu := muSof_facts hW hN
  have hae := ae_UH_of_quot hG.2.2.1 hmu.1 hmu.2 hq
  by_cases hnz : ∃ x ∈ DDsp σ w0, ∃ y ∈ DDsp σ w0, be z c π σ μW μN x y ≠ 0
  · obtain ⟨l, hl, -, hid⟩ := hSh hIn k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS hnz
    refine ⟨l, hl, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), hid x (hsm x hx) v hv⟩, ?_⟩
    intro x hx hx0 v hv
    have hNv := (hNI hIn hSch k r ε lam h H σ w0 Wp z c u π μW μN μG νq hS x (hsm x hx) v (Or.inl hv) (l v)).1
    rw [hid v (hsm v hv) v hv] at hNv
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply] at hNv
    rw [hdeg w0 hw0n] at hNv
    rw [hdeg x hx0]
    refine l2_norm_scaling _ _ (l v) _ _ (by positivity) hNv (hae.mono fun g hg => ?_)
    rw [hid _ (PI.UnitaryGroupMassFormula.CapelliEig.smooth_right_action k r ε lam H σ hσ x (hsm x hx) _ hg) v hv]
    simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply]
  · push_neg at hnz
    refine ⟨fun _ => 0, bessel_zero, fun x hx v hv => ⟨hBC1 x (hsm x hx) v (Or.inl hv), ?_⟩,
      fun x _ _ v _ => by simp⟩
    show be z c π σ μW μN x v = _
    rw [hnz x hx v hv]
    ext ξ; simp
end Formalism.FourierDecayAlt.P.DDSmoothness
