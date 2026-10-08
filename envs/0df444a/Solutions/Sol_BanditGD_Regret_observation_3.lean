-- Prove2me | solution 1 for BanditGD.Regret.observation_3
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-06T05:18:29.98606+00:00
-- url     : https://prove2.me/submissions/e8f74ae4-977f-4ef9-9951-7cd3d302338e

import Mathlib
open scoped Pointwise

set_option autoImplicit false

namespace P96e24d05

lemma ball_sub {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hrS : Metric.closedBall 0 r ⊆ S) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ (1 - α) • S) (w : EuclideanSpace ℝ (Fin d))
    (hw : ‖w - x‖ ≤ α * r) : w ∈ S := by
  obtain ⟨s, hs, rfl⟩ := Set.mem_smul_set.mp hx
  have hz : α⁻¹ • (w - (1 - α) • s) ∈ S := by
    apply hrS
    rw [Metric.mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos hα0, inv_mul_le_iff₀ hα0]
    exact hw
  have := hSconv hs hz (by linarith : (0:ℝ) ≤ 1 - α) hα0.le (by ring)
  convert this using 1
  rw [smul_smul, mul_inv_cancel₀ hα0.ne', one_smul]
  abel

end P96e24d05

open scoped Pointwise in
theorem solution {d : ℕ} (S : Set (EuclideanSpace ℝ (Fin d))) (hSconv : Convex ℝ S)
    (r : ℝ) (hr : 0 < r) (hrS : Metric.closedBall 0 r ⊆ S) (α : ℝ) (hα0 : 0 < α) (hα1 : α ≤ 1)
    (C : ℝ) (f : EuclideanSpace ℝ (Fin d) → ℝ) (hf : ConvexOn ℝ S f) (hfC : ∀ x ∈ S, |f x| ≤ C) :
    ∀ x ∈ (1 - α) • S, ∀ y ∈ S, |f x - f y| ≤ 2 * C / (α * r) * ‖x - y‖ := by
  intro x hx y hy
  have hρ : 0 < α * r := mul_pos hα0 hr
  set ρ := α * r with hρdef
  have hxS : x ∈ S := P96e24d05.ball_sub S hSconv r hrS α hα0 hα1 x hx x (by simpa using hρ.le)
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hfC x hxS)
  have bnd : ∀ u ∈ S, ∀ v ∈ S, f u - f v ≤ 2 * C := by
    intro u hu v hv
    have h1 := (abs_le.mp (hfC u hu)).2
    have h2 := (abs_le.mp (hfC v hv)).1
    linarith
  set t := ‖x - y‖ with htdef
  rcases (norm_nonneg (x - y)).eq_or_lt with h0 | ht
  · have hxy : x = y := sub_eq_zero.mp (norm_eq_zero.mp h0.symm)
    have ht0 : t = 0 := h0.symm
    rw [ht0, mul_zero, hxy, sub_self, abs_zero]
  have ht : 0 < t := ht
  have htne : t ≠ 0 := ht.ne'
  have hρt : ρ + t ≠ 0 := by positivity
  have hrw : 2 * C / ρ * t = 2 * C * (t / ρ) := by ring
  rw [hrw, abs_sub_le_iff]
  constructor
  · -- f x - f y
    set z := x + (ρ / t) • (x - y) with hzdef
    have hzS : z ∈ S := by
      apply P96e24d05.ball_sub S hSconv r hrS α hα0 hα1 x hx z
      rw [hzdef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ ht),
        ← htdef, div_mul_cancel₀ _ ht.ne']
    have hsum : ρ / (ρ + t) + t / (ρ + t) = 1 := by
      field_simp
    have hcomb : (ρ / (ρ + t)) • y + (t / (ρ + t)) • z = x := by
      have e : (ρ / (ρ + t)) • y + (t / (ρ + t)) • z
          = ((t / (ρ + t)) + (t / (ρ + t)) * (ρ / t)) • x
            + ((ρ / (ρ + t)) - (t / (ρ + t)) * (ρ / t)) • y := by
        rw [hzdef]; module
      have c1 : (t / (ρ + t)) + (t / (ρ + t)) * (ρ / t) = 1 := by
        field_simp
        ring
      have c2 : (ρ / (ρ + t)) - (t / (ρ + t)) * (ρ / t) = 0 := by
        field_simp; ring
      rw [e, c1, c2, one_smul, zero_smul, add_zero]
    have hconv := hf.2 hy hzS (div_pos hρ (by linarith)).le (div_pos ht (by linarith)).le hsum
    rw [hcomb, smul_eq_mul, smul_eq_mul] at hconv
    have hb : t / (ρ + t) ≤ t / ρ := div_le_div_of_nonneg_left ht.le hρ (by linarith)
    have hzy := bnd z hzS y hy
    have ha : ρ / (ρ + t) = 1 - t / (ρ + t) := by linarith
    rw [ha] at hconv
    have hb0 : 0 ≤ t / (ρ + t) := (div_pos ht (by linarith)).le
    nlinarith
  · -- f y - f x
    rcases le_or_gt ρ t with hle | hlt
    · have h1 : 1 ≤ t / ρ := (one_le_div hρ).mpr hle
      have := bnd y hy x hxS
      nlinarith
    · set w := x + (ρ / t) • (y - x) with hwdef
      have hwS : w ∈ S := by
        apply P96e24d05.ball_sub S hSconv r hrS α hα0 hα1 x hx w
        rw [hwdef, add_sub_cancel_left, norm_smul, Real.norm_eq_abs, abs_of_pos (div_pos hρ ht),
          norm_sub_rev, ← htdef, div_mul_cancel₀ _ ht.ne']
      have hcomb : (1 - t / ρ) • x + (t / ρ) • w = y := by
        have e : (1 - t / ρ) • x + (t / ρ) • w
            = (1 - t / ρ + t / ρ - (t / ρ) * (ρ / t)) • x + ((t / ρ) * (ρ / t)) • y := by
          rw [hwdef]; module
        have c1 : (t / ρ) * (ρ / t) = 1 := by field_simp
        rw [e, c1, one_smul, sub_add_cancel, sub_self, zero_smul, zero_add]
      have h1 : 0 ≤ 1 - t / ρ := by
        have : t / ρ < 1 := (div_lt_one hρ).mpr hlt
        linarith
      have hsum : (1 - t / ρ) + t / ρ = 1 := by ring
      have hconv := hf.2 hxS hwS h1 (div_pos ht hρ).le hsum
      rw [hcomb, smul_eq_mul, smul_eq_mul] at hconv
      have := bnd w hwS x hxS
      nlinarith [div_pos ht hρ]
