-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann.hasFDerivAt_prim
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T07:32:14.603174+00:00
-- url     : https://prove2.me/submissions/ee27f847-e1f5-43d7-87f3-7ce4f413a4ba

import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasDerivAtTMul
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_HasFDerivAtPrim
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_seg_mem
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_seg_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_continuous_seg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasDerivAt_seg
import Theorems.Thm_Formalism_FourierDecayAlt_P_CutMP_Gauge_GC_Ann_hasFDerivAt_seg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Set Filter Topology MeasureTheory intervalIntegral Metric
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.CutMP Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
noncomputable section
variable {ω : ℂ → ℂ →L[ℝ] ℝ} {S : Set ℂ} {w₀ : ℂ}
namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
theorem _root_.solution (hS : IsOpen S) (hc : Convex ℝ S) (hw₀ : w₀ ∈ S) (hω : ContDiffOn ℝ 1 ω S)
    (hsym : ∀ p ∈ S, ∀ h k : ℂ, fderiv ℝ ω p h k = fderiv ℝ ω p k h) {w : ℂ} (hw : w ∈ S) :
    HasFDerivAt (prim ω w₀) (ω w) w := by
  have hdiff : ∀ p ∈ S, HasFDerivAt ω (fderiv ℝ ω p) p := fun p hp =>
    (((hω.differentiableOn one_ne_zero) p hp).differentiableAt (hS.mem_nhds hp)).hasFDerivAt
  have hcontω : ContinuousOn ω S := hω.continuousOn
  have hcontD : ContinuousOn (fderiv ℝ ω) S := hω.continuousOn_fderiv_of_isOpen hS le_rfl
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hS w hw
  set δ' := δ / 2 with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hcb : closedBall w δ' ⊆ S := (closedBall_subset_ball (by linarith)).trans hball
  set K := (fun p : ℂ × ℝ => seg w₀ p.1 p.2) '' (closedBall w δ' ×ˢ Icc (0 : ℝ) 1) with hK
  have hKc : IsCompact K := ((isCompact_closedBall w δ').prod isCompact_Icc).image continuous_seg
  have hKS : K ⊆ S := by
    rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
    exact seg_mem hc hw₀ (hcb hx) ht
  have hmemK : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1, seg w₀ x t ∈ K := fun x hx t ht =>
    ⟨(x, t), ⟨hx, ht⟩, rfl⟩
  obtain ⟨M₁, hM₁⟩ := hKc.exists_bound_of_continuousOn (hcontω.mono hKS)
  obtain ⟨M₂, hM₂⟩ := hKc.exists_bound_of_continuousOn (hcontD.mono hKS)
  set F' : ℂ → ℝ → (ℂ →L[ℝ] ℝ) := fun x t => ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)
    with hF'
  have hFd : ∀ x ∈ closedBall w δ', ∀ t ∈ Icc (0 : ℝ) 1,
      HasFDerivAt (fun y => ω (seg w₀ y t) (y - w₀)) (F' x t) x := by
    intro x hx t ht
    have hs := hmemK x hx t ht
    have hc1 : HasFDerivAt (fun y => ω (seg w₀ y t)) ((fderiv ℝ ω (seg w₀ x t)).comp ((t : ℂ) • ContinuousLinearMap.id ℝ ℂ)) x :=
      (hdiff _ (hKS hs)).comp x (hasFDerivAt_seg x t)
    have hu : HasFDerivAt (fun y : ℂ => y - w₀) (ContinuousLinearMap.id ℝ ℂ) x := (hasFDerivAt_id x).sub_const w₀
    have h := hc1.clm_apply hu
    refine h.congr_fderiv ?_
    ext h'
    simp only [hF', ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.flip_apply, ContinuousLinearMap.smul_apply]
    rw [show ((t : ℂ) • h' : ℂ) = (t : ℝ) • h' from by rw [Complex.real_smul]; rfl, map_smul]
    simp
  have hseg_cont : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => seg w₀ x t) (Icc 0 1) := fun x _ =>
    (continuous_seg.comp (Continuous.prodMk continuous_const continuous_id)).continuousOn
  have hωseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontω.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hDseg : ∀ x ∈ closedBall w δ', ContinuousOn (fun t : ℝ => fderiv ℝ ω (seg w₀ x t)) (Icc 0 1) := fun x hx =>
    hcontD.comp (hseg_cont x hx) fun t ht => hKS (hmemK x hx t ht)
  have hF'cont : ∀ x ∈ closedBall w δ', ContinuousOn (F' x) (Icc 0 1) := by
    intro x hx
    refine (hωseg x hx).add (ContinuousOn.smul continuousOn_id ?_)
    exact ((ContinuousLinearMap.flipₗᵢ ℝ ℂ ℂ ℝ).continuous.comp_continuousOn (hDseg x hx)).clm_apply continuousOn_const
  have hIoc : Set.uIoc (0 : ℝ) 1 = Ioc 0 1 := uIoc_of_le zero_le_one
  have hwc : w ∈ closedBall w δ' := mem_closedBall_self hδ'0.le
  have hLeib := intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun y t => ω (seg w₀ y t) (y - w₀)) (F' := F') (x₀ := w) (a := 0) (b := 1)
    (bound := fun _ => M₁ + M₂ * (δ' + ‖w - w₀‖)) (s := ball w δ') (ball_mem_nhds w hδ'0) ?_ ?_ ?_ ?_ intervalIntegrable_const ?_
  · have hint : ∫ t in (0 : ℝ)..1, F' w t = ω w := by
      have hEq : EqOn (F' w) (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        simp only [hF']
        congr 2
        ext h'
        simp only [ContinuousLinearMap.flip_apply]
        exact hsym _ hs h' (w - w₀)
      rw [intervalIntegral.integral_congr hEq]
      have hd : ∀ t ∈ uIcc (0 : ℝ) 1, HasDerivAt (fun s : ℝ => s • ω (seg w₀ w s))
          (ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) t := by
        intro t ht
        rw [uIcc_of_le zero_le_one] at ht
        have hs := hKS (hmemK w hwc t ht)
        have h1 := (hdiff _ hs).comp_hasDerivAt t (hasDerivAt_seg (w₀ := w₀) w t)
        have h2 := (hasDerivAt_id t).smul h1
        refine h2.congr_deriv ?_
        simp only [id, one_smul]
        abel
      have hcd : ContinuousOn (fun t => ω (seg w₀ w t) + t • fderiv ℝ ω (seg w₀ w t) (w - w₀)) (uIcc 0 1) := by
        rw [uIcc_of_le zero_le_one]
        exact (hωseg w hwc).add (continuousOn_id.smul ((hDseg w hwc).clm_apply continuousOn_const))
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcd.intervalIntegrable)]
      simp [seg_one]
    rw [← hint]
    exact hLeib
  · filter_upwards [ball_mem_nhds w hδ'0] with x hx
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    rw [hIoc]
    exact (((hωseg x hxc).clm_apply continuousOn_const).mono Ioc_subset_Icc_self).aestronglyMeasurable
      measurableSet_Ioc
  · refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le zero_le_one]
    exact (hωseg w hwc).clm_apply continuousOn_const
  · rw [hIoc]
    exact ((hF'cont w hwc).mono Ioc_subset_Icc_self).aestronglyMeasurable measurableSet_Ioc
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    have ht' : t ∈ Icc (0 : ℝ) 1 := Ioc_subset_Icc_self ht
    have hxc : x ∈ closedBall w δ' := ball_subset_closedBall hx
    have hs := hmemK x hxc t ht'
    have h1 : ‖ω (seg w₀ x t)‖ ≤ M₁ := hM₁ _ hs
    have h2 : ‖fderiv ℝ ω (seg w₀ x t)‖ ≤ M₂ := hM₂ _ hs
    have h3 : ‖x - w₀‖ ≤ δ' + ‖w - w₀‖ := by
      have := norm_sub_le_norm_sub_add_norm_sub x w w₀
      have hxw : ‖x - w‖ ≤ δ' := by rw [← dist_eq_norm]; exact mem_closedBall.mp hxc
      linarith
    have hM₂0 : 0 ≤ M₂ := le_trans (norm_nonneg _) h2
    simp only [hF']
    calc ‖ω (seg w₀ x t) + t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖
        ≤ ‖ω (seg w₀ x t)‖ + ‖t • (fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ := norm_add_le _ _
      _ ≤ M₁ + M₂ * (δ' + ‖w - w₀‖) := by
        refine add_le_add h1 ?_
        rw [norm_smul]
        have hf : ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ M₂ * (δ' + ‖w - w₀‖) := by
          refine ((fderiv ℝ ω (seg w₀ x t)).flip.le_opNorm (x - w₀)).trans ?_
          rw [ContinuousLinearMap.opNorm_flip]
          exact mul_le_mul h2 h3 (norm_nonneg _) hM₂0
        have ht1 : ‖t‖ ≤ 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht'.1]; exact ht'.2
        calc ‖t‖ * ‖(fderiv ℝ ω (seg w₀ x t)).flip (x - w₀)‖ ≤ 1 * (M₂ * (δ' + ‖w - w₀‖)) :=
              mul_le_mul ht1 hf (norm_nonneg _) zero_le_one
          _ = M₂ * (δ' + ‖w - w₀‖) := one_mul _
  · refine Eventually.of_forall fun t ht x hx => ?_
    rw [hIoc] at ht
    exact hFd x (ball_subset_closedBall hx) t (Ioc_subset_Icc_self ht)
end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC.Ann
