-- Prove2me | solution 1 for Complex.norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/ff83d7da-3bff-5c2d-884a-1479ac3fd6c4

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp

set_option autoImplicit false

open Complex Metric Set Filter
open scoped Topology

namespace R4BC

theorem bc_bound_le {M R x : ℝ} (hM : 0 < M) (hR : 0 < R) {θ : ℝ} (_hθ0 : 0 < θ) (hθ1 : θ < 1)
    (_hx0 : 0 ≤ x) (hx : x ≤ θ * R) :
    2 * (2 * M) * x / (R - x) ≤ 4 * M * θ / (1 - θ) := by
  have hRx : 0 < R - x := by nlinarith
  have h1θ : 0 < 1 - θ := by linarith
  rw [div_le_div_iff₀ hRx h1θ]
  nlinarith [mul_pos hM hR]

theorem main (F : ℂ → ℂ) (s₀ : ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hd : DifferentiableOn ℂ F (ball s₀ R))
    (hnz : ∀ z ∈ ball s₀ R, F z ≠ 0)
    (hup : ∀ z ∈ ball s₀ R, ‖F z‖ ≤ Real.exp M)
    (hlo : Real.exp (-M) ≤ ‖F s₀‖) :
    ∀ s ∈ closedBall s₀ (R / 2),
      ‖deriv F s‖ ≤ 48 * M / R * ‖F s‖ ∧ Real.exp (-(5 * M)) ≤ ‖F s‖ := by
  have hs₀ : s₀ ∈ ball s₀ R := mem_ball_self hR
  have hF₀ : F s₀ ≠ 0 := hnz s₀ hs₀
  have hF₀pos : 0 < ‖F s₀‖ := norm_pos_iff.mpr hF₀

  have hFan : AnalyticOnNhd ℂ F (ball s₀ R) := hd.analyticOnNhd isOpen_ball
  have hF'd : DifferentiableOn ℂ (deriv F) (ball s₀ R) := hFan.deriv.differentiableOn
  set q : ℂ → ℂ := fun z => deriv F z / F z with hqdef
  have hqd : DifferentiableOn ℂ q (ball s₀ R) := hF'd.div hd hnz
  obtain ⟨g, hg₀, hg⟩ := (hqd.isExactOn_ball).with_val_at s₀ 0
  have hgd : DifferentiableOn ℂ g (ball s₀ R) := fun z hz =>
    (hg z hz).differentiableAt.differentiableWithinAt

  have hconst : ∀ z ∈ ball s₀ R, F z * cexp (-(g z)) = F s₀ := by
    intro z hz
    have hderiv : ∀ w ∈ ball s₀ R, HasDerivAt (fun w => F w * cexp (-(g w))) 0 w := by
      intro w hw
      have hF : HasDerivAt F (deriv F w) w :=
        (hd.differentiableAt (isOpen_ball.mem_nhds hw)).hasDerivAt
      have hG : HasDerivAt (fun w => cexp (-(g w))) (cexp (-(g w)) * (-(q w))) w :=
        (hg w hw).neg.cexp
      have h := hF.mul hG
      have hzero : deriv F w * cexp (-(g w)) + F w * (cexp (-(g w)) * -q w) = 0 := by
        rw [hqdef]
        field_simp [hnz w hw]
        ring
      rwa [hzero] at h
    have hdiff : DifferentiableOn ℂ (fun w => F w * cexp (-(g w))) (ball s₀ R) := fun w hw =>
      (hderiv w hw).differentiableAt.differentiableWithinAt
    have h := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball s₀ R).isPreconnected hdiff
      (fun w hw => by rw [(hderiv w hw).deriv]; rfl) hz hs₀
    rw [h, hg₀, neg_zero, exp_zero, mul_one]
  have hFeq : ∀ z ∈ ball s₀ R, F z = F s₀ * cexp (g z) := by
    intro z hz
    have h := hconst z hz
    calc F z = F z * cexp (-(g z)) * cexp (g z) := by
          rw [mul_assoc, ← exp_add, neg_add_cancel, exp_zero, mul_one]
      _ = F s₀ * cexp (g z) := by rw [h]
  have hnormF : ∀ z ∈ ball s₀ R, ‖F z‖ = ‖F s₀‖ * Real.exp (g z).re := by
    intro z hz; rw [hFeq z hz, norm_mul, norm_exp]

  have hgre : ∀ z ∈ ball s₀ R, (g z).re ≤ 2 * M := by
    intro z hz
    have h1 : ‖F s₀‖ * Real.exp (g z).re ≤ Real.exp M := by rw [← hnormF z hz]; exact hup z hz
    have h2 : Real.exp (-M) * Real.exp (g z).re ≤ Real.exp M :=
      le_trans (mul_le_mul_of_nonneg_right hlo (Real.exp_pos _).le) h1
    rw [← Real.exp_add, Real.exp_le_exp] at h2
    linarith

  set G : ℂ → ℂ := fun w => g (s₀ + w) with hGdef
  have hshift : ∀ {w : ℂ}, w ∈ ball (0 : ℂ) R → s₀ + w ∈ ball s₀ R := by
    intro w hw
    rw [mem_ball, dist_eq_norm] at hw ⊢
    simpa using hw
  have hGd : DifferentiableOn ℂ G (ball 0 R) := by
    intro w hw
    have h : DifferentiableAt ℂ g (s₀ + w) := (hg _ (hshift hw)).differentiableAt
    exact (h.comp w ((differentiableAt_const s₀).add differentiableAt_id)).differentiableWithinAt
  have hGmaps : MapsTo G (ball 0 R) {z : ℂ | z.re ≤ 2 * M} := fun w hw => hgre _ (hshift hw)
  have hG0 : G 0 = 0 := by simp [hGdef, hg₀]
  have hBC : ∀ w ∈ ball (0 : ℂ) R, ‖G w‖ ≤ 2 * (2 * M) * ‖w‖ / (R - ‖w‖) := fun w hw =>
    Complex.borelCaratheodory_zero (by positivity) hGd hGmaps hR hw hG0

  have hgbound : ∀ {θ : ℝ}, 0 < θ → θ < 1 → ∀ z : ℂ, ‖z - s₀‖ ≤ θ * R →
      ‖g z‖ ≤ 4 * M * θ / (1 - θ) := by
    intro θ hθ0 hθ1 z hz
    have hw : z - s₀ ∈ ball (0 : ℂ) R := by
      rw [mem_ball, dist_zero_right]
      calc ‖z - s₀‖ ≤ θ * R := hz
        _ < 1 * R := mul_lt_mul_of_pos_right hθ1 hR
        _ = R := one_mul R
    have h := hBC (z - s₀) hw
    have heq : G (z - s₀) = g z := by simp [hGdef]
    rw [heq] at h
    exact h.trans (bc_bound_le hM hR hθ0 hθ1 (norm_nonneg _) hz)
  have hg_half : ∀ z : ℂ, ‖z - s₀‖ ≤ R / 2 → ‖g z‖ ≤ 4 * M := by
    intro z hz
    have h := hgbound (θ := 1 / 2) (by norm_num) (by norm_num) z (by linarith)
    norm_num at h
    linarith
  have hg_34 : ∀ z : ℂ, ‖z - s₀‖ ≤ 3 * R / 4 → ‖g z‖ ≤ 12 * M := by
    intro z hz
    have h := hgbound (θ := 3 / 4) (by norm_num) (by norm_num) z (by linarith)
    norm_num at h
    linarith

  intro s hs
  rw [mem_closedBall, dist_eq_norm] at hs
  have hsball : s ∈ ball s₀ R := by
    rw [mem_ball, dist_eq_norm]; linarith
  have hlow : Real.exp (-(5 * M)) ≤ ‖F s‖ := by
    rw [hnormF s hsball]
    have h1 : -(4 * M) ≤ (g s).re := by
      have := abs_re_le_norm (g s)
      have := neg_le_of_abs_le this
      linarith [hg_half s hs]
    calc Real.exp (-(5 * M)) = Real.exp (-M) * Real.exp (-(4 * M)) := by
          rw [← Real.exp_add]; ring_nf
      _ ≤ ‖F s₀‖ * Real.exp (g s).re :=
          mul_le_mul hlo (Real.exp_le_exp.mpr h1) (Real.exp_pos _).le hF₀pos.le
  refine ⟨?_, hlow⟩

  have hR4 : 0 < R / 4 := by positivity
  have hsub : closedBall s (R / 4) ⊆ ball s₀ R := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm] at hz
    rw [mem_ball, dist_eq_norm]
    calc ‖z - s₀‖ = ‖(z - s) + (s - s₀)‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s - s₀‖ := norm_add_le _ _
      _ < R := by linarith
  have hgdc : DiffContOnCl ℂ g (ball s (R / 4)) := hgd.diffContOnCl_ball hsub
  have hsphere : ∀ z ∈ sphere s (R / 4), ‖g z‖ ≤ 12 * M := by
    intro z hz
    rw [mem_sphere, dist_eq_norm] at hz
    refine hg_34 z ?_
    calc ‖z - s₀‖ = ‖(z - s) + (s - s₀)‖ := by ring_nf
      _ ≤ ‖z - s‖ + ‖s - s₀‖ := norm_add_le _ _
      _ ≤ 3 * R / 4 := by linarith
  have hderivg : ‖deriv g s‖ ≤ 12 * M / (R / 4) :=
    Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR4 hgdc hsphere
  have hgs : deriv g s = deriv F s / F s := (hg s hsball).deriv
  have hFs : F s ≠ 0 := hnz s hsball
  have hkey : ‖deriv F s‖ = ‖deriv g s‖ * ‖F s‖ := by
    rw [hgs, norm_div, div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hFs)]
  rw [hkey]
  refine mul_le_mul_of_nonneg_right (hderivg.trans (le_of_eq ?_)) (norm_nonneg _)
  field_simp
  ring

end R4BC

theorem solution
    (F : ℂ → ℂ) (s₀ : ℂ) (R M : ℝ) (hR : 0 < R) (hM : 0 < M)
    (hd : DifferentiableOn ℂ F (Metric.ball s₀ R))
    (hnz : ∀ z ∈ Metric.ball s₀ R, F z ≠ 0)
    (hup : ∀ z ∈ Metric.ball s₀ R, ‖F z‖ ≤ Real.exp M)
    (hlo : Real.exp (-M) ≤ ‖F s₀‖) :
    ∀ s ∈ Metric.closedBall s₀ (R / 2),
      ‖deriv F s‖ ≤ 48 * M / R * ‖F s‖ ∧ Real.exp (-(5 * M)) ≤ ‖F s‖ :=
  R4BC.main F s₀ R M hR hM hd hnz hup hlo

end S_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp
end P2MW
export P2MW.S_Complex_norm_deriv_le_mul_norm_and_exp_neg_le_norm_of_forall_ne_zero_of_norm_le_exp (solution)
