-- Prove2me | solution 1 for Complex.hasDerivAt_circleIntegral_mul_deriv_div_sub
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/f705bff9-eb08-5aa0-bae3-8dcfef494031

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub

open scoped Real

namespace CircleLogIntegralLevel

open Complex Metric MeasureTheory

variable {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ}

theorem exists_pos_le_norm_sub (hr : 0 < r) (hΦ : ∀ z ∈ sphere z₀ r, AnalyticAt ℂ Φ z)
    (hne : ∀ z ∈ sphere z₀ r, Φ z ≠ t₀) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ z ∈ sphere z₀ r, δ ≤ ‖Φ z - t₀‖ := by
  have hcont : ContinuousOn (fun z => ‖Φ z - t₀‖) (sphere z₀ r) := fun z hz =>
    ((hΦ z hz).continuousAt.sub continuousAt_const).norm.continuousWithinAt
  obtain ⟨x, hx, hmin⟩ := (isCompact_sphere z₀ r).exists_isMinOn
    ((NormedSpace.sphere_nonempty (x := z₀)).2 hr.le) hcont
  refine ⟨‖Φ x - t₀‖, norm_pos_iff.2 (sub_ne_zero.2 (hne x hx)), fun z hz => ?_⟩
  exact (isMinOn_iff.1 hmin) z hz

theorem norm_deriv_circleMap_le (hr : 0 < r) (θ : ℝ) : ‖deriv (circleMap z₀ r) θ‖ ≤ r := by
  rw [deriv_circleMap]
  simp [circleMap, abs_of_pos hr]

theorem circleIntegral_mul_deriv_div_sq_eq (hr : 0 < r)
    (hΦ : ∀ z ∈ sphere z₀ r, AnalyticAt ℂ Φ z) (hG : ∀ z ∈ sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ sphere z₀ r, Φ z ≠ t₀) :
    (∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t₀) ^ 2) =
      ∮ z in C(z₀, r), deriv G z / (Φ z - t₀) := by

  have hH : ∀ z ∈ sphere z₀ r, HasDerivWithinAt (fun y => G y / (Φ y - t₀))
      ((deriv G z * (Φ z - t₀) - G z * deriv Φ z) / (Φ z - t₀) ^ 2) (sphere z₀ r) z := by
    intro z hz
    have h1 : HasDerivAt G (deriv G z) z := (hG z hz).differentiableAt.hasDerivAt
    have h2 : HasDerivAt (fun y => Φ y - t₀) (deriv Φ z) z :=
      (hΦ z hz).differentiableAt.hasDerivAt.sub_const t₀
    exact (h1.div h2 (sub_ne_zero.2 (hne z hz))).hasDerivWithinAt
  have h0 := circleIntegral.integral_eq_zero_of_hasDerivWithinAt hr.le hH

  have cG : ContinuousOn G (sphere z₀ r) := fun z hz => (hG z hz).continuousAt.continuousWithinAt
  have cG' : ContinuousOn (deriv G) (sphere z₀ r) := fun z hz =>
    (hG z hz).deriv.continuousAt.continuousWithinAt
  have cΦ' : ContinuousOn (deriv Φ) (sphere z₀ r) := fun z hz =>
    (hΦ z hz).deriv.continuousAt.continuousWithinAt
  have cD : ContinuousOn (fun z => Φ z - t₀) (sphere z₀ r) := fun z hz =>
    ((hΦ z hz).continuousAt.sub continuousAt_const).continuousWithinAt
  have hD0 : ∀ z ∈ sphere z₀ r, Φ z - t₀ ≠ 0 := fun z hz => sub_ne_zero.2 (hne z hz)
  have cA : ContinuousOn (fun z => deriv G z / (Φ z - t₀)) (sphere z₀ r) := cG'.div cD hD0
  have cB : ContinuousOn (fun z => G z * deriv Φ z / (Φ z - t₀) ^ 2) (sphere z₀ r) :=
    (cG.mul cΦ').div (cD.pow 2) fun z hz => pow_ne_zero 2 (hD0 z hz)

  have hcongr : (∮ z in C(z₀, r), (deriv G z * (Φ z - t₀) - G z * deriv Φ z) / (Φ z - t₀) ^ 2) =
      ∮ z in C(z₀, r), (deriv G z / (Φ z - t₀) - G z * deriv Φ z / (Φ z - t₀) ^ 2) := by
    refine circleIntegral.integral_congr hr.le fun z hz => ?_
    have h := hD0 z hz
    field_simp
  rw [hcongr, circleIntegral.integral_sub (cA.circleIntegrable hr.le) (cB.circleIntegrable hr.le)]
    at h0
  exact (sub_eq_zero.1 h0).symm

end CircleLogIntegralLevel

open CircleLogIntegralLevel Complex Metric MeasureTheory in
theorem solution
    {Φ G : ℂ → ℂ} {z₀ t₀ : ℂ} {r : ℝ} (hr : 0 < r)
    (hΦ : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ Φ z)
    (hG : ∀ z ∈ Metric.sphere z₀ r, AnalyticAt ℂ G z)
    (hne : ∀ z ∈ Metric.sphere z₀ r, Φ z ≠ t₀) :
    HasDerivAt (fun t : ℂ => ∮ z in C(z₀, r), G z * deriv Φ z / (Φ z - t))
      (∮ z in C(z₀, r), deriv G z / (Φ z - t₀)) t₀ := by
  obtain ⟨δ, hδ, hδle⟩ := exists_pos_le_norm_sub hr hΦ hne

  have cG : ContinuousOn G (sphere z₀ r) := fun z hz => (hG z hz).continuousAt.continuousWithinAt
  have cΦ : ContinuousOn Φ (sphere z₀ r) := fun z hz => (hΦ z hz).continuousAt.continuousWithinAt
  have cΦ' : ContinuousOn (deriv Φ) (sphere z₀ r) := fun z hz =>
    (hΦ z hz).deriv.continuousAt.continuousWithinAt
  obtain ⟨MG, hMG⟩ := (isCompact_sphere z₀ r).exists_bound_of_continuousOn cG
  obtain ⟨MΦ, hMΦ⟩ := (isCompact_sphere z₀ r).exists_bound_of_continuousOn cΦ'
  have hMG0 : 0 ≤ MG := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := z₀)).2 hr.le
    exact (norm_nonneg _).trans (hMG x hx)
  have hMΦ0 : 0 ≤ MΦ := by
    obtain ⟨x, hx⟩ := (NormedSpace.sphere_nonempty (x := z₀)).2 hr.le
    exact (norm_nonneg _).trans (hMΦ x hx)

  have hlow : ∀ t ∈ ball t₀ (δ / 2), ∀ z ∈ sphere z₀ r, δ / 2 ≤ ‖Φ z - t‖ := by
    intro t ht z hz
    have h1 := hδle z hz
    have h2 : ‖t - t₀‖ < δ / 2 := by rwa [mem_ball, dist_eq_norm] at ht
    have h3 : ‖Φ z - t₀‖ ≤ ‖Φ z - t‖ + ‖t - t₀‖ := by
      calc ‖Φ z - t₀‖ = ‖(Φ z - t) + (t - t₀)‖ := by ring_nf
        _ ≤ ‖Φ z - t‖ + ‖t - t₀‖ := norm_add_le _ _
    linarith
  have hne' : ∀ t ∈ ball t₀ (δ / 2), ∀ z ∈ sphere z₀ r, Φ z - t ≠ 0 := by
    intro t ht z hz h
    have := hlow t ht z hz
    rw [h, norm_zero] at this
    linarith

  set F : ℂ → ℝ → ℂ := fun t θ =>
    deriv (circleMap z₀ r) θ • (G (circleMap z₀ r θ) * deriv Φ (circleMap z₀ r θ) /
      (Φ (circleMap z₀ r θ) - t)) with hF
  set F' : ℂ → ℝ → ℂ := fun t θ =>
    deriv (circleMap z₀ r) θ • (G (circleMap z₀ r θ) * deriv Φ (circleMap z₀ r θ) /
      (Φ (circleMap z₀ r θ) - t) ^ 2) with hF'
  have hsph : ∀ θ : ℝ, circleMap z₀ r θ ∈ sphere z₀ r := fun θ => circleMap_mem_sphere z₀ hr.le θ
  have hcd : Continuous (deriv (circleMap z₀ r)) :=
    (contDiff_circleMap z₀ r).continuous_deriv le_top

  have hFc : ∀ t ∈ ball t₀ (δ / 2), Continuous (F t) := by
    intro t ht
    have hK : ContinuousOn (fun z => G z * deriv Φ z / (Φ z - t)) (sphere z₀ r) :=
      (cG.mul cΦ').div (cΦ.sub continuousOn_const) (hne' t ht)
    exact hcd.smul (hK.comp_continuous (continuous_circleMap z₀ r) hsph)
  have hF'c : ∀ t ∈ ball t₀ (δ / 2), Continuous (F' t) := by
    intro t ht
    have hK : ContinuousOn (fun z => G z * deriv Φ z / (Φ z - t) ^ 2) (sphere z₀ r) :=
      (cG.mul cΦ').div ((cΦ.sub continuousOn_const).pow 2)
        fun z hz => pow_ne_zero 2 (hne' t ht z hz)
    exact hcd.smul (hK.comp_continuous (continuous_circleMap z₀ r) hsph)
  have ht₀ : t₀ ∈ ball t₀ (δ / 2) := mem_ball_self (half_pos hδ)

  have key := intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (𝕜 := ℂ) (μ := volume) (a := 0) (b := 2 * π) (F := F) (F' := F') (x₀ := t₀)
    (s := ball t₀ (δ / 2)) (bound := fun _ => r * (MG * MΦ / (δ / 2) ^ 2))
    (ball_mem_nhds t₀ (half_pos hδ))
    (by
      filter_upwards [ball_mem_nhds t₀ (half_pos hδ)] with t ht
      exact (hFc t ht).aestronglyMeasurable)
    ((hFc t₀ ht₀).intervalIntegrable 0 (2 * π))
    (hF'c t₀ ht₀).aestronglyMeasurable
    (by
      refine Filter.Eventually.of_forall fun θ _ t ht => ?_
      have hz := hsph θ
      have hlo := hlow t ht _ hz
      have hpos : 0 < ‖Φ (circleMap z₀ r θ) - t‖ := lt_of_lt_of_le (half_pos hδ) hlo
      simp only [hF', norm_smul, norm_div, norm_mul, norm_pow]
      have hnum : ‖G (circleMap z₀ r θ)‖ * ‖deriv Φ (circleMap z₀ r θ)‖ ≤ MG * MΦ :=
        mul_le_mul (hMG _ hz) (hMΦ _ hz) (norm_nonneg _) hMG0
      have hden : (δ / 2) ^ 2 ≤ ‖Φ (circleMap z₀ r θ) - t‖ ^ 2 :=
        pow_le_pow_left₀ (half_pos hδ).le hlo 2
      have hfrac : ‖G (circleMap z₀ r θ)‖ * ‖deriv Φ (circleMap z₀ r θ)‖ /
          ‖Φ (circleMap z₀ r θ) - t‖ ^ 2 ≤ MG * MΦ / (δ / 2) ^ 2 :=
        div_le_div₀ (mul_nonneg hMG0 hMΦ0) hnum (pow_pos (half_pos hδ) 2) hden
      exact mul_le_mul (norm_deriv_circleMap_le hr θ) hfrac
        (div_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (pow_nonneg (norm_nonneg _) 2))
        hr.le)
    intervalIntegrable_const
    (by
      refine Filter.Eventually.of_forall fun θ _ t ht => ?_
      have hz := hsph θ
      have hne0 : Φ (circleMap z₀ r θ) - t ≠ 0 := hne' t ht _ hz
      have h1 : HasDerivAt (fun s : ℂ => Φ (circleMap z₀ r θ) - s) (-1) t := by
        simpa using (hasDerivAt_id t).const_sub (Φ (circleMap z₀ r θ))
      have h2 := (h1.inv hne0).const_mul (G (circleMap z₀ r θ) * deriv Φ (circleMap z₀ r θ))
      have h3 := h2.const_smul (deriv (circleMap z₀ r) θ)
      refine (h3.congr_deriv ?_).congr_of_eventuallyEq ?_
      · simp only [hF', neg_neg, one_mul, div_eq_mul_inv]
      · exact Filter.Eventually.of_forall fun s => by
          simp only [hF, div_eq_mul_inv, Pi.smul_apply, Pi.inv_apply, smul_eq_mul])
  have hd := key.2

  have hval : (∫ θ in (0 : ℝ)..2 * π, F' t₀ θ) = ∮ z in C(z₀, r), deriv G z / (Φ z - t₀) := by
    rw [← circleIntegral_mul_deriv_div_sq_eq hr hΦ hG hne]
    rfl
  rw [hval] at hd
  exact hd

end S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub
end P2MW
export P2MW.S_Complex_hasDerivAt_circleIntegral_mul_deriv_div_sub (solution)
