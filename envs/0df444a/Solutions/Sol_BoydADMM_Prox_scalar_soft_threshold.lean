-- Prove2me | solution 1 for BoydADMM.Prox.scalar_soft_threshold
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T18:20:40.44698+00:00
-- url     : https://prove2.me/submissions/328b2c30-41f0-4947-9edc-70c7b4f9084d

import Mathlib
import Definitions.Def_BoydADMM_Prox_Basic

open Matrix


namespace BoydADMM.Prox

theorem shrink_core (κ : ℝ) (hκ : 0 ≤ κ) (a : ℝ) (ha : a ≠ 0) :
    softThreshold κ a = max (1 - κ / |a|) 0 * a := by
  unfold softThreshold
  rcases lt_or_gt_of_ne ha with h | h
  · rw [abs_of_neg h]
    have hpos : 0 < -a := by linarith
    split_ifs with h1 h2
    · linarith
    · have : κ / -a < 1 := by rw [div_lt_one hpos]; linarith
      rw [max_eq_left (by linarith)]
      field_simp; ring
    · have : 1 ≤ κ / -a := by rw [le_div_iff₀ hpos]; linarith
      rw [max_eq_right (by linarith)]; ring
  · rw [abs_of_pos h]
    split_ifs with h1 h2
    · have : κ / a < 1 := by rw [div_lt_one h]; linarith
      rw [max_eq_left (by linarith)]
      field_simp
    · linarith
    · have : 1 ≤ κ / a := by rw [le_div_iff₀ h]; linarith
      rw [max_eq_right (by linarith)]; ring

/-- strong optimality of soft thresholding -/
theorem st_strong (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) (a s : ℝ) :
    lam * |softThreshold (lam / ρ) a| + (ρ / 2) * (softThreshold (lam / ρ) a - a) ^ 2
      + (ρ / 2) * (s - softThreshold (lam / ρ) a) ^ 2 ≤ lam * |s| + (ρ / 2) * (s - a) ^ 2 := by
  set κ := lam / ρ with hκdef
  have hlk : lam = κ * ρ := by rw [hκdef]; field_simp
  have hκ : 0 < κ := div_pos hlam hρ
  rw [hlk]
  unfold softThreshold
  have hs1 : s ≤ |s| := le_abs_self s
  have hs2 : -s ≤ |s| := neg_le_abs s
  split_ifs with h1 h2
  · rw [abs_of_pos (by linarith : (0:ℝ) < a - κ)]
    nlinarith [mul_le_mul_of_nonneg_left hs1 (le_of_lt (mul_pos hκ hρ))]
  · rw [abs_of_neg (by linarith : a + κ < 0)]
    nlinarith [mul_le_mul_of_nonneg_left hs2 (le_of_lt (mul_pos hκ hρ))]
  · push_neg at h1 h2
    simp only [abs_zero, mul_zero, zero_add, zero_sub, sub_zero]
    have : a * s ≤ κ * |s| := by
      rcases le_total 0 s with hs | hs
      · rw [abs_of_nonneg hs]; nlinarith
      · rw [abs_of_nonpos hs]; nlinarith
    nlinarith [mul_le_mul_of_nonneg_left this hρ.le]

theorem scalar_core (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) (a t : ℝ) :
    (∀ s : ℝ, lam * |t| + (ρ / 2) * (t - a) ^ 2 ≤ lam * |s| + (ρ / 2) * (s - a) ^ 2) ↔
      t = softThreshold (lam / ρ) a := by
  constructor
  · intro h
    have h1 := h (softThreshold (lam / ρ) a)
    have h2 := st_strong lam ρ hlam hρ a t
    have : (ρ / 2) * (t - softThreshold (lam / ρ) a) ^ 2 ≤ 0 := by linarith
    have h3 : (t - softThreshold (lam / ρ) a) ^ 2 ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have : t - softThreshold (lam / ρ) a = 0 := by nlinarith [sq_nonneg (t - softThreshold (lam / ρ) a)]
    linarith
  · rintro rfl s
    have := st_strong lam ρ hlam hρ a s
    nlinarith [sq_nonneg (s - softThreshold (lam / ρ) a)]

theorem l1_core {n : ℕ} (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ)
    (v x : EuclideanSpace ℝ (Fin n)) :
    IsProx Set.univ (fun y => lam * l1Norm y) ρ v x ↔ x = softThresholdVec (lam / ρ) v := by
  have nsq : ∀ y : EuclideanSpace ℝ (Fin n), ‖y‖ ^ 2 = ∑ i, (y i) ^ 2 := by
    intro y; rw [EuclideanSpace.norm_sq_eq]; simp [Real.norm_eq_abs, sq_abs]
  set S := softThresholdVec (lam / ρ) v with hS
  have hSi : ∀ i, S i = softThreshold (lam / ρ) (v i) := fun i => rfl
  -- strong inequality
  have strong : ∀ y : EuclideanSpace ℝ (Fin n),
      lam * l1Norm S + (ρ / 2) * ‖S - v‖ ^ 2 + (ρ / 2) * ‖y - S‖ ^ 2 ≤
        lam * l1Norm y + (ρ / 2) * ‖y - v‖ ^ 2 := by
    intro y
    simp only [nsq, l1Norm, Finset.mul_sum, PiLp.sub_apply, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    rw [hSi]
    exact st_strong lam ρ hlam hρ (v i) (y i)
  constructor
  · rintro ⟨-, h⟩
    have h1 := h S (Set.mem_univ _)
    have h2 := strong x
    have : (ρ / 2) * ‖x - S‖ ^ 2 ≤ 0 := by simp only at h1; linarith
    have h3 : ‖x - S‖ ^ 2 ≤ 0 := by
      by_contra hc; push_neg at hc; nlinarith
    have : ‖x - S‖ = 0 := by nlinarith [norm_nonneg (x - S)]
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  · rintro rfl
    refine ⟨Set.mem_univ _, fun y _ => ?_⟩
    have := strong y
    simp only
    nlinarith [sq_nonneg ‖y - S‖]

end BoydADMM.Prox

open BoydADMM.Prox


theorem solution (lam ρ : ℝ) (hlam : 0 < lam) (hρ : 0 < ρ) (a t : ℝ) :
    (∀ s : ℝ, lam * |t| + (ρ / 2) * (t - a) ^ 2 ≤ lam * |s| + (ρ / 2) * (s - a) ^ 2) ↔
      t = softThreshold (lam / ρ) a := by
  exact scalar_core lam ρ hlam hρ a t
