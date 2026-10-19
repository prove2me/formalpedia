-- Prove2me | solution 1 for CohnElkies.saddleGaussian_fullLine_error_le_central_add_tails
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:32.057836+00:00
-- url     : https://prove2.me/submissions/d7a94d35-afac-44fb-8968-df6f13b57c9d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleGaussian_central_compl_subset_tail

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {F G : ℝ → ℂ}
    (hF : Integrable F) (hG : Integrable G)
    (R : ℝ) :
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ ≤
      ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) := by
  let s : Set ℝ := Icc (-R) R
  let tail : Set ℝ := saddleGaussianTailSet R
  have hsub : sᶜ ⊆ tail :=
    saddleGaussian_central_compl_subset_tail R
  have hsubae : sᶜ ≤ᶠ[ae (volume : Measure ℝ)] tail :=
    Filter.Eventually.of_forall (fun T hT => hsub hT)
  have hdiff : Integrable (fun T : ℝ => F T - G T) :=
    hF.sub hG
  have hmonoF :
      (∫ T : ℝ in sᶜ, ‖F T‖) ≤
        ∫ T : ℝ in tail, ‖F T‖ := by
    apply setIntegral_mono_set hF.norm.integrableOn
    · exact Filter.Eventually.of_forall (fun T => norm_nonneg (F T))
    · exact hsubae
  have hmonoG :
      (∫ T : ℝ in sᶜ, ‖G T‖) ≤
        ∫ T : ℝ in tail, ‖G T‖ := by
    apply setIntegral_mono_set hG.norm.integrableOn
    · exact Filter.Eventually.of_forall (fun T => norm_nonneg (G T))
    · exact hsubae
  have hpoint : ∀ T ∈ sᶜ,
      ‖F T - G T‖ ≤ ‖F T‖ + ‖G T‖ := by
    intro T hT
    exact norm_sub_le _ _
  have hcompare := setIntegral_mono_on
    hdiff.norm.integrableOn
    (hF.norm.add hG.norm).integrableOn
    (measurableSet_Icc.compl) hpoint
  have htailbound :
      ‖∫ T : ℝ in sᶜ, (F T - G T)‖ ≤
        (∫ T : ℝ in tail, ‖F T‖) +
          (∫ T : ℝ in tail, ‖G T‖) := by
    calc
      ‖∫ T : ℝ in sᶜ, (F T - G T)‖ ≤
          ∫ T : ℝ in sᶜ, ‖F T - G T‖ :=
        MeasureTheory.norm_integral_le_integral_norm _
      _ ≤ ∫ T : ℝ in sᶜ, (‖F T‖ + ‖G T‖) := hcompare
      _ = (∫ T : ℝ in sᶜ, ‖F T‖) +
          (∫ T : ℝ in sᶜ, ‖G T‖) := by
        rw [integral_add hF.norm.integrableOn
          hG.norm.integrableOn]
      _ ≤ (∫ T : ℝ in tail, ‖F T‖) +
          (∫ T : ℝ in tail, ‖G T‖) :=
        add_le_add hmonoF hmonoG
  have hsplit := integral_add_compl
    (μ := volume) (f := fun T : ℝ => F T - G T) (s := s)
      (show MeasurableSet s from measurableSet_Icc) hdiff
  calc
    ‖(∫ T : ℝ, F T) - (∫ T : ℝ, G T)‖ =
        ‖∫ T : ℝ, (F T - G T)‖ := by
          rw [integral_sub hF hG]
    _ = ‖(∫ T : ℝ in s, (F T - G T)) +
          (∫ T : ℝ in sᶜ, (F T - G T))‖ := by
          rw [hsplit]
    _ ≤ ‖∫ T : ℝ in s, (F T - G T)‖ +
          ‖∫ T : ℝ in sᶜ, (F T - G T)‖ :=
          norm_add_le _ _
    _ ≤ ‖∫ T : ℝ in s, (F T - G T)‖ +
          ((∫ T : ℝ in tail, ‖F T‖) +
            (∫ T : ℝ in tail, ‖G T‖)) := by
          gcongr
    _ = ‖∫ T : ℝ in Icc (-R) R, (F T - G T)‖ +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖F T‖) +
        (∫ T : ℝ in saddleGaussianTailSet R, ‖G T‖) := by
          try dsimp [s, tail]
          ring
end CohnElkies
