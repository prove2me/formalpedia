-- Prove2me | solution 1 for FickDiffusion.mean_squared_displacement
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T05:32:00.463233+00:00
-- url     : https://prove2.me/submissions/dc48513a-725f-4a0b-84a0-ff373b3ec586

import Mathlib
import Definitions.Def_FickDiffusion_defs

open Real Filter Topology MeasureTheory

namespace FickMSD

lemma moment (n : ℕ) (hn : 1 ≤ n) (b : ℝ) (hb : 0 < b) (k : ℕ) :
    ∫ y in Set.Ioi (0:ℝ), y ^ (n - 1) • (y ^ (2 * k) * exp (-b * y ^ 2)) =
      b ^ (-((n:ℝ) + 2 * k) / 2) * (1 / 2) * Gamma (((n:ℝ) + 2 * k) / 2) := by
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n:ℝ) - 1 + 2 * k) (b := b)
    (by norm_num) (by have : (1:ℝ) ≤ n := by exact_mod_cast hn
                      have : (0:ℝ) ≤ k := k.cast_nonneg
                      linarith) hb
  rw [show (n:ℝ) - 1 + 2 * k + 1 = n + 2 * k by ring] at h
  rw [← h]
  refine setIntegral_congr_fun measurableSet_Ioi (fun y hy => ?_)
  have hy : (0:ℝ) < y := hy
  simp only [smul_eq_mul]
  rw [show ((n:ℝ) - 1 + 2 * k) = ((n - 1 + 2 * k : ℕ) : ℝ) by push_cast [Nat.cast_sub hn]; ring,
    rpow_natCast, show (2:ℝ) = ((2:ℕ):ℝ) by norm_num, rpow_natCast, pow_add]
  ring

lemma moment2 (n : ℕ) (hn : 1 ≤ n) (b : ℝ) (hb : 0 < b) :
    ∫ y in Set.Ioi (0:ℝ), y ^ (n - 1) * (y ^ 2 * exp (-b * y ^ 2)) =
      b ^ (-((n:ℝ) + 2) / 2) * (1 / 2) * Gamma (((n:ℝ) + 2) / 2) := by
  have := moment n hn b hb 1
  norm_num at this ⊢
  exact this

lemma moment0 (n : ℕ) (hn : 1 ≤ n) (b : ℝ) (hb : 0 < b) :
    ∫ y in Set.Ioi (0:ℝ), y ^ (n - 1) * exp (-b * y ^ 2) =
      b ^ (-(n:ℝ) / 2) * (1 / 2) * Gamma ((n:ℝ) / 2) := by
  have := moment n hn b hb 0
  norm_num at this ⊢
  exact this

end FickMSD

open FickMSD in
theorem solution (n : ℕ) (D t : ℝ) (hD : 0 < D) (ht : 0 < t) :
    ∫ x, ‖x‖ ^ 2 * FickDiffusion.heatKernelEuclid n D x t = 2 * n * D * t := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · have h0 : ∀ x : EuclideanSpace ℝ (Fin 0), x = 0 := fun x => Subsingleton.elim _ _
    simp [h0]
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  set b := 1 / (4 * D * t) with hbdef
  have hb : 0 < b := by positivity
  set c := (4 * π * D * t) ^ (-(n : ℝ) / 2) with hc
  have h1 : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 * FickDiffusion.heatKernelEuclid n D x t =
      c * (‖x‖ ^ 2 * exp (-b * ‖x‖ ^ 2)) := by
    intro x
    unfold FickDiffusion.heatKernelEuclid
    simp only [hc, hbdef]; ring_nf
  simp_rw [h1]
  rw [integral_const_mul]
  have hI := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun y => y ^ 2 * exp (-b * y ^ 2))
  have hJ := integral_fun_norm_addHaar (volume : Measure (EuclideanSpace ℝ (Fin n)))
    (fun y => exp (-b * y ^ 2))
  have hG := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := EuclideanSpace ℝ (Fin n)) hb
  simp only [finrank_euclideanSpace_fin, nsmul_eq_mul, smul_eq_mul] at hI hJ hG
  rw [hI, moment2 n hn b hb]
  rw [hG, moment0 n hn b hb] at hJ
  have hΓ : Gamma (((n:ℝ) + 2) / 2) = ((n:ℝ) / 2) * Gamma ((n:ℝ) / 2) := by
    rw [show ((n:ℝ) + 2) / 2 = (n:ℝ) / 2 + 1 by ring, Gamma_add_one (by positivity)]
  have hbp : b ^ (-((n:ℝ) + 2) / 2) = b ^ (-(n:ℝ) / 2) * b⁻¹ := by
    rw [← rpow_neg_one, ← rpow_add hb]; congr 1; ring
  rw [hΓ, hbp]
  have : (n:ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
      (b ^ (-(n:ℝ) / 2) * b⁻¹ * (1 / 2) * ((n:ℝ) / 2 * Gamma ((n:ℝ) / 2)))) =
      ((n:ℝ) * ((volume : Measure (EuclideanSpace ℝ (Fin n))).real (Metric.ball 0 1) *
      (b ^ (-(n:ℝ) / 2) * (1 / 2) * Gamma ((n:ℝ) / 2)))) * ((n:ℝ) / (2 * b)) := by
    field_simp
  rw [this, ← hJ]
  have hpb : π / b = 4 * π * D * t := by rw [hbdef]; field_simp
  rw [hpb, hc, ← mul_assoc, ← rpow_add (by positivity)]
  rw [show -(n:ℝ) / 2 + (n:ℝ) / 2 = 0 by ring, rpow_zero, one_mul, hbdef]
  field_simp
  norm_num
