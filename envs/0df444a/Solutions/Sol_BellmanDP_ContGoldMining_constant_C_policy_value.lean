-- Prove2me | solution 1 for BellmanDP.ContGoldMining.constant_C_policy_value
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-10-07T12:29:59.229993+00:00
-- url     : https://prove2.me/submissions/69152caf-38c9-4ca6-b8c3-1ccf5bf456c5

import Mathlib
import Definitions.Def_BellmanDP_ContGoldMining_Process



namespace BellmanDP.ContGoldMining

open MeasureTheory Set

lemma cgm_lint_two_exp (A B α β : ℝ) (hα : 0 < α) (hβ : 0 < β) (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ∫⁻ t in Ioi (0:ℝ), ENNReal.ofReal (A * Real.exp (-α * t) + B * Real.exp (-β * t)) =
      ENNReal.ofReal (A / α + B / β) := by
  have h1 : IntegrableOn (fun t : ℝ => Real.exp (-α * t)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hα
  have h2 : IntegrableOn (fun t : ℝ => Real.exp (-β * t)) (Ioi 0) := exp_neg_integrableOn_Ioi 0 hβ
  have hi : IntegrableOn (fun t : ℝ => A * Real.exp (-α * t) + B * Real.exp (-β * t)) (Ioi 0) :=
    (h1.const_mul A).add (h2.const_mul B)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall (fun t => by
    positivity))]
  congr 1
  rw [integral_add (h1.const_mul A) (h2.const_mul B), integral_const_mul, integral_const_mul,
    integral_exp_mul_Ioi (by linarith) 0, integral_exp_mul_Ioi (by linarith) 0]
  simp only [mul_zero, Real.exp_zero]
  field_simp

lemma cgm_cumTime_const (φ : Control) (c : Fin 3 → ℝ) (hc : ∀ i t, φ i t = c i) (i : Fin 3)
    (t : ℝ) : cumTime φ i t = c i * t := by
  unfold cumTime
  simp only [hc, intervalIntegral.integral_const, smul_eq_mul, sub_zero]
  ring

theorem constant_policy_values_core (q₁ q₂ r₁ r₂ x₀ y₀ : ℝ) (hq₁ : 0 < q₁) (hq₂ : 0 < q₂)
    (hr₁ : 0 < r₁) (hr₂ : 0 < r₂) (hx₀ : 0 ≤ x₀) (hy₀ : 0 ≤ y₀) :
    goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice fun _ => 1) =
        ENNReal.ofReal (r₁ * x₀ / (q₁ + r₁)) ∧
      goldInfty (Params.two q₁ q₂ r₁ r₂) x₀ y₀ (twoChoice fun _ => 0) =
        ENNReal.ofReal (r₂ * y₀ / (q₂ + r₂)) := by
  constructor
  · have hc := cgm_cumTime_const (twoChoice fun _ => 1) ![1, 0, 0]
      (fun i t => by fin_cases i <;> simp [twoChoice])
    unfold goldInfty
    rw [show r₁ * x₀ / (q₁ + r₁) = (r₁ * x₀) / (q₁ + r₁) + 0 / 1 by ring,
      ← cgm_lint_two_exp (r₁ * x₀) 0 (q₁ + r₁) 1 (by linarith) one_pos (by positivity) le_rfl]
    congr 1; funext t; congr 1
    simp only [goldRate, survival, stateX, stateY, hc, Fin.sum_univ_three, twoChoice,
      Params.q, Params.a, Params.b, Params.two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    simp only [zero_mul, mul_zero, add_zero, sub_self, one_mul, mul_one, zero_add]
    rw [show -(q₁ + r₁) * t = -(q₁ * t) + -(r₁ * t) by ring, Real.exp_add]
    ring
  · have hc := cgm_cumTime_const (twoChoice fun _ => 0) ![0, 1, 0]
      (fun i t => by fin_cases i <;> simp [twoChoice])
    unfold goldInfty
    rw [show r₂ * y₀ / (q₂ + r₂) = (r₂ * y₀) / (q₂ + r₂) + 0 / 1 by ring,
      ← cgm_lint_two_exp (r₂ * y₀) 0 (q₂ + r₂) 1 (by linarith) one_pos (by positivity) le_rfl]
    congr 1; funext t; congr 1
    simp only [goldRate, survival, stateX, stateY, hc, Fin.sum_univ_three, twoChoice,
      Params.q, Params.a, Params.b, Params.two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
    simp only [zero_mul, mul_zero, add_zero, sub_self, one_mul, mul_one, zero_add, sub_zero]
    rw [show -(q₂ + r₂) * t = -(q₂ * t) + -(r₂ * t) by ring, Real.exp_add]
    ring

theorem constant_C_policy_value_core (P : Params) (hP : P.Positive) (x₀ y₀ : ℝ) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) :
    goldInfty P x₀ y₀ (fun i _ => ![0, 0, 1] i) =
      ENNReal.ofReal (P.r₃ * x₀ / (P.q₃ + P.r₃) + P.r₄ * y₀ / (P.q₃ + P.r₄)) := by
  obtain ⟨hq1, hq2, hq3, hr1, hr2, hr3, hr4⟩ := hP
  have hc := cgm_cumTime_const (fun i _ => ![0, 0, 1] i) ![0, 0, 1] (fun i t => rfl)
  unfold goldInfty
  rw [← cgm_lint_two_exp (P.r₃ * x₀) (P.r₄ * y₀) (P.q₃ + P.r₃) (P.q₃ + P.r₄) (by linarith)
    (by linarith) (by positivity) (by positivity)]
  congr 1; funext t; congr 1
  simp only [goldRate, survival, stateX, stateY, hc, Fin.sum_univ_three,
    Params.q, Params.a, Params.b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val]
  simp only [zero_mul, mul_zero, add_zero, one_mul, mul_one, zero_add]
  rw [show -(P.q₃ + P.r₃) * t = -(P.q₃ * t) + -(P.r₃ * t) by ring,
    show -(P.q₃ + P.r₄) * t = -(P.q₃ * t) + -(P.r₄ * t) by ring, Real.exp_add, Real.exp_add]
  ring

end BellmanDP.ContGoldMining

open BellmanDP.ContGoldMining


theorem solution (P : Params) (hP : P.Positive) (x₀ y₀ : ℝ) (hx₀ : 0 ≤ x₀)
    (hy₀ : 0 ≤ y₀) :
    goldInfty P x₀ y₀ (fun i _ => ![0, 0, 1] i) =
      ENNReal.ofReal (P.r₃ * x₀ / (P.q₃ + P.r₃) + P.r₄ * y₀ / (P.q₃ + P.r₄)) := by
  exact constant_C_policy_value_core P hP x₀ y₀ hx₀ hy₀
