-- Prove2me | solution 1 for Complex.exists_analyticOnNhd_comp_pow_of_forall_mul_eq
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.491319+00:00
-- url     : https://prove2.me/submissions/92f40a6e-ca52-58f8-89ca-166967d3dd2b

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq

open Metric

theorem solution {e : ℕ} (he : 0 < e) {ω : ℂ} (hω : IsPrimitiveRoot ω e)
    {f : ℂ → ℂ} {r : ℝ} (hr : 0 < r) (hf : AnalyticOnNhd ℂ f (Metric.ball 0 r))
    (hinv : ∀ z ∈ Metric.ball 0 r, f (ω * z) = f z) :
    ∃ F : ℂ → ℂ, AnalyticOnNhd ℂ F (Metric.ball 0 (r ^ e)) ∧ ∀ z ∈ Metric.ball 0 r, f z = F (z ^ e) := by
  classical
  haveI : NeZero e := NeZero.of_pos he
  have he0 : e ≠ 0 := he.ne'
  have hω1 : ‖ω‖ = 1 := hω.norm'_eq_one he0

  have hinvj : ∀ (j : ℕ), ∀ z ∈ Metric.ball (0 : ℂ) r, f (ω ^ j * z) = f z := by
    intro j
    induction j with
    | zero => intro z _; simp
    | succ j ih =>
      intro z hz
      have hmem : ω ^ j * z ∈ Metric.ball (0 : ℂ) r := by
        rw [mem_ball_zero_iff] at hz ⊢
        simpa [norm_mul, norm_pow, hω1] using hz
      rw [pow_succ', mul_assoc, hinv _ hmem, ih z hz]

  have hroots : ∀ a b : ℂ, b ≠ 0 → a ^ e = b ^ e → ∃ j : ℕ, a = ω ^ j * b := by
    intro a b hb hab
    have h1 : (a / b) ^ e = 1 := by rw [div_pow, hab, div_self (pow_ne_zero _ hb)]
    obtain ⟨j, -, hj⟩ := hω.eq_pow_of_pow_eq_one h1
    exact ⟨j, by rw [hj, div_mul_cancel₀ _ hb]⟩

  have hnorm : ∀ z : ℂ, ‖z‖ < r ↔ ‖z ^ e‖ < r ^ e := fun z => by
    rw [norm_pow]
    exact (pow_lt_pow_iff_left₀ (norm_nonneg _) hr.le he0).symm

  have hex : ∀ w : ℂ, ∃ z : ℂ, z ^ e = w := fun w => IsAlgClosed.exists_pow_nat_eq w he
  choose root hroot using hex
  have hroot0 : root 0 = 0 := by simpa [he0] using hroot 0
  set F : ℂ → ℂ := fun w => f (root w) with hF

  have hFroot : ∀ z ∈ Metric.ball (0 : ℂ) r, F (z ^ e) = f z := by
    intro z hz
    rcases eq_or_ne z 0 with rfl | hz0
    · simp [hF, zero_pow he0, hroot0]
    · obtain ⟨j, hj⟩ := hroots (root (z ^ e)) z hz0 (hroot _)
      simp only [hF]
      rw [hj, hinvj j z hz]
  refine ⟨F, fun w₀ hw₀ => ?_, fun z hz => (hFroot z hz).symm⟩

  have hAt : ∀ w₀ ∈ Metric.ball (0 : ℂ) (r ^ e), w₀ ≠ 0 → AnalyticAt ℂ F w₀ := by
    intro w₀ hw₀ hw₀0
    set z₀ := root w₀ with hz₀
    have hz₀e : z₀ ^ e = w₀ := hroot w₀
    have hz₀0 : z₀ ≠ 0 := by
      rintro h0
      rw [h0, zero_pow he0] at hz₀e
      exact hw₀0 hz₀e.symm
    set ρ : ℂ → ℂ := fun w => z₀ * Complex.exp (Complex.log (w / w₀) / e) with hρ
    have hρan : AnalyticAt ℂ ρ w₀ := by
      have h1 : AnalyticAt ℂ Complex.log (w₀ / w₀) := by
        rw [div_self hw₀0]; exact analyticAt_clog Complex.one_mem_slitPlane
      have h2 : AnalyticAt ℂ (fun w : ℂ => w / w₀) w₀ := analyticAt_id.div_const
      have h3 : AnalyticAt ℂ (fun w : ℂ => Complex.exp (Complex.log (w / w₀) / (e : ℂ))) w₀ := by
        have := ((AnalyticAt.comp (f := fun w : ℂ => w / w₀) h1 h2).div_const (c := (e : ℂ))).cexp
        exact this
      exact analyticAt_const.mul h3
    have hρe : ∀ w, w ≠ 0 → ρ w ^ e = w := by
      intro w hw
      simp only [hρ]
      rw [mul_pow, hz₀e, ← Complex.exp_nat_mul, mul_div_cancel₀ _ (Nat.cast_ne_zero.2 he0),
        Complex.exp_log (div_ne_zero hw hw₀0), mul_div_cancel₀ _ hw₀0]
    have hρball : ∀ w ∈ Metric.ball (0 : ℂ) (r ^ e), w ≠ 0 → ρ w ∈ Metric.ball (0 : ℂ) r := by
      intro w hw hw0
      rw [mem_ball_zero_iff] at hw ⊢
      rw [hnorm, hρe w hw0]
      exact hw
    have hFρ : (f ∘ ρ) =ᶠ[nhds w₀] F := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hw₀, isOpen_ne.mem_nhds hw₀0] with w hwb hw0
      have hρw0 : ρ w ≠ 0 := by
        intro h0
        have := hρe w hw0
        rw [h0, zero_pow he0] at this
        exact hw0 this.symm
      obtain ⟨j, hj⟩ := hroots (root w) (ρ w) hρw0 (by rw [hroot, hρe w hw0])
      simp only [Function.comp_apply, hF]
      rw [hj, hinvj j (ρ w) (hρball w hwb hw0)]
    exact ((hf (ρ w₀) (hρball w₀ hw₀ hw₀0)).comp hρan).congr hFρ
  rcases eq_or_ne w₀ 0 with rfl | hw₀0
  ·
    apply Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hw₀), self_mem_nhdsWithin] with w hwb hw0
      exact (hAt w hwb hw0).differentiableAt
    · rw [Metric.continuousAt_iff]
      intro ε hε
      obtain ⟨δ, hδ, hfδ⟩ := Metric.continuousAt_iff.mp (hf 0 (Metric.mem_ball_self hr)).continuousAt ε hε
      refine ⟨δ ^ e, pow_pos hδ e, fun w hw => ?_⟩
      simp only [hF, hroot0]
      apply hfδ
      rw [dist_zero_right] at hw ⊢
      rw [← hroot w, norm_pow] at hw
      exact lt_of_pow_lt_pow_left₀ e hδ.le hw
  · exact hAt w₀ hw₀ hw₀0

end S_Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq
end P2MW
export P2MW.S_Complex_exists_analyticOnNhd_comp_pow_of_forall_mul_eq (solution)
