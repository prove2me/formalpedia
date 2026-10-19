-- Prove2me | solution 1 for CarneiroDeSitter.bose_integral_number_of_states
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-17T06:57:32.220622+00:00
-- url     : https://prove2.me/submissions/533af235-db13-453a-8067-ac0d6f8eed5e

import Mathlib
import Definitions.Def_CarneiroDeSitter2006

open Real Filter Topology MeasureTheory Set

namespace BoseAux

lemma term_integral (k : ℕ) (n : ℕ) :
    ∫ x in Ioi (0:ℝ), x ^ k * Real.exp (-((n:ℝ) + 1) * x) = (k.factorial : ℝ) / ((n:ℝ) + 1) ^ (k + 1) := by
  have hb : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h := integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := (k:ℝ)) (b := (n:ℝ) + 1) one_pos
    (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) hb
  have e1 : ∫ x in Ioi (0:ℝ), x ^ k * Real.exp (-((n:ℝ) + 1) * x)
      = ∫ x in Ioi (0:ℝ), x ^ (k:ℝ) * Real.exp (-((n:ℝ) + 1) * x ^ (1:ℝ)) := by
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    simp [Real.rpow_natCast]
  rw [e1, h, div_one, div_one, div_one, Real.Gamma_nat_eq_factorial, Real.rpow_neg hb.le,
    show ((k:ℝ) + 1) = ((k + 1 : ℕ) : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp [div_eq_mul_inv, mul_comm]

lemma term_integrable (k : ℕ) (n : ℕ) :
    IntegrableOn (fun x : ℝ => x ^ k * Real.exp (-((n:ℝ) + 1) * x)) (Ioi 0) := by
  have hb : (0:ℝ) < (n:ℝ) + 1 := by positivity
  have h := integrableOn_rpow_mul_exp_neg_mul_rpow (p := 1) (s := (k:ℝ)) (b := (n:ℝ) + 1)
    (by have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith) one_pos hb
  refine h.congr_fun (fun x hx => ?_) measurableSet_Ioi
  simp [Real.rpow_natCast]

lemma geom (k : ℕ) (x : ℝ) (hx : 0 < x) :
    ∑' n : ℕ, x ^ k * Real.exp (-((n:ℝ) + 1) * x) = x ^ k / (Real.exp x - 1) := by
  have hr0 : 0 ≤ Real.exp (-x) := (Real.exp_pos _).le
  have hr1 : Real.exp (-x) < 1 := Real.exp_lt_one_iff.2 (by linarith)
  have e : ∀ n : ℕ, x ^ k * Real.exp (-((n:ℝ) + 1) * x) = x ^ k * Real.exp (-x) * Real.exp (-x) ^ n := by
    intro n
    rw [← Real.exp_nat_mul, mul_assoc, ← Real.exp_add]; congr 2; ring
  simp_rw [e]
  rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1]
  have hex : 1 < Real.exp x := Real.one_lt_exp_iff.2 hx
  have h1 : Real.exp (-x) = (Real.exp x)⁻¹ := Real.exp_neg x
  rw [h1]
  have : Real.exp x - 1 ≠ 0 := by linarith
  have : 1 - (Real.exp x)⁻¹ ≠ 0 := by
    have : (Real.exp x)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hex
    linarith
  field_simp

theorem bose (k : ℕ) (hk : 1 ≤ k) :
    ∫ x in Ioi (0:ℝ), x ^ k / (Real.exp x - 1) = (k.factorial : ℝ) * ∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ (k + 1) := by
  have hs : Summable (fun n : ℕ => 1 / ((n:ℝ) + 1) ^ (k + 1)) := by
    have := (Real.summable_one_div_nat_pow (p := k + 1)).2 (by omega)
    have := (summable_nat_add_iff 1).2 this
    simpa using this
  have H := hasSum_integral_of_summable_integral_norm (μ := volume.restrict (Ioi (0:ℝ)))
    (F := fun (n : ℕ) (x : ℝ) => x ^ k * Real.exp (-((n:ℝ) + 1) * x))
    (fun n => term_integrable k n) (by
      have e : ∀ n : ℕ, ∫ x in Ioi (0:ℝ), ‖x ^ k * Real.exp (-((n:ℝ) + 1) * x)‖
          = (k.factorial : ℝ) * (1 / ((n:ℝ) + 1) ^ (k + 1)) := by
        intro n
        rw [mul_one_div, ← term_integral k n]
        refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
        simp only [Real.norm_eq_abs]
        exact abs_of_nonneg (mul_nonneg (pow_nonneg (le_of_lt hx) _) (Real.exp_pos _).le)
      simp_rw [e]
      exact hs.mul_left _)
  have e2 : ∫ x in Ioi (0:ℝ), (∑' n : ℕ, x ^ k * Real.exp (-((n:ℝ) + 1) * x))
      = ∫ x in Ioi (0:ℝ), x ^ k / (Real.exp x - 1) :=
    setIntegral_congr_fun measurableSet_Ioi (fun x hx => geom k x hx)
  rw [← e2, ← H.tsum_eq]
  simp_rw [term_integral, div_eq_mul_one_div (k.factorial : ℝ)]
  rw [tsum_mul_left]

/-- Scaled version. -/
theorem bose_scaled (k : ℕ) (hk : 1 ≤ k) (M : ℝ) (hM : 0 < M) :
    ∫ ω in Ioi (0:ℝ), ω ^ k / (Real.exp (ω / M) - 1)
      = M ^ (k + 1) * ((k.factorial : ℝ) * ∑' n : ℕ, 1 / ((n:ℝ) + 1) ^ (k + 1)) := by
  rw [← bose k hk]
  have h := integral_comp_mul_left_Ioi (fun ω => ω ^ k / (Real.exp (ω / M) - 1)) 0 hM
  simp only [mul_zero, smul_eq_mul] at h
  have e : ∫ x in Ioi (0:ℝ), (M * x) ^ k / (Real.exp (M * x / M) - 1)
      = M ^ k * ∫ x in Ioi (0:ℝ), x ^ k / (Real.exp x - 1) := by
    rw [← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Ioi (fun x hx => ?_)
    rw [mul_div_cancel_left₀ x hM.ne', mul_pow, mul_div_assoc]
  rw [e] at h
  have : ∫ ω in Ioi (0:ℝ), ω ^ k / (Real.exp (ω / M) - 1) = M * (M ^ k * ∫ x in Ioi (0:ℝ), x ^ k / (Real.exp x - 1)) := by
    rw [h]; field_simp
  rw [this]; ring

end BoseAux

open Real Filter Topology Asymptotics MeasureTheory Set CarneiroDeSitter

theorem solution (m H : ℝ) (hm : 0 < m) (hH : 0 ≤ H) :
    ∫ ω in Ioi (0 : ℝ), ω ^ 2 / (Real.exp (ω / (m + H)) - 1)
      = 2 * (∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ 3) * (m + H) ^ 3 := by
  rw [BoseAux.bose_scaled 2 (by norm_num) (m + H) (by linarith)]
  simp [Nat.factorial]
  ring
