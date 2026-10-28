-- Prove2me | solution 1 for CouplingHMC.Exact.eq_119_120
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:44:38.068965+00:00
-- url     : https://prove2.me/submissions/0a55fbf8-a521-4023-baa6-c124b5ab555d

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace Aux_CHMC119

lemma te (x y : ℝ) (hx : 1 ≤ x) (hxy : x ≤ y) : y * Real.exp (-y) ≤ x * Real.exp (-x) := by
  have h1 := Real.add_one_le_exp (y - x)
  have h2 : y ≤ x * Real.exp (y - x) := by nlinarith
  have h3 : y * Real.exp (-y) ≤ x * Real.exp (y - x) * Real.exp (-y) :=
    mul_le_mul_of_nonneg_right h2 (Real.exp_pos _).le
  rw [mul_assoc, ← Real.exp_add] at h3
  have : y - x + -y = -x := by ring
  rw [this] at h3
  exact h3

lemma core (x y : ℝ) (hx : 0 < x) (hxy : x ≤ y) :
    max 1 y * Real.exp (-y) * (1 - Real.exp (-x)) ≤ x * Real.exp (-x) := by
  have h1 : 1 - Real.exp (-x) ≤ x := by have := Real.add_one_le_exp (-x); linarith
  have hpos : 0 ≤ 1 - Real.exp (-x) := by
    have : Real.exp (-x) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    linarith
  have hey : Real.exp (-y) ≤ Real.exp (-x) := Real.exp_le_exp.mpr (by linarith)
  rcases le_or_gt y 1 with hy | hy
  · rw [max_eq_left hy, one_mul]
    calc Real.exp (-y) * (1 - Real.exp (-x)) ≤ Real.exp (-x) * x :=
          mul_le_mul hey h1 hpos (Real.exp_pos _).le
      _ = x * Real.exp (-x) := by ring
  · rw [max_eq_right hy.le]
    rcases le_or_gt 1 x with hx1 | hx1
    · have := te x y hx1 hxy
      have h2 : 1 - Real.exp (-x) ≤ 1 := by linarith [Real.exp_pos (-x)]
      calc y * Real.exp (-y) * (1 - Real.exp (-x)) ≤ x * Real.exp (-x) * 1 :=
            mul_le_mul this h2 hpos (by positivity)
        _ = x * Real.exp (-x) := by ring
    · have h3 := te 1 y le_rfl hy.le
      have h4 : 1 * Real.exp (-1) ≤ Real.exp (-x) := by
        rw [one_mul]; exact Real.exp_le_exp.mpr (by linarith)
      calc y * Real.exp (-y) * (1 - Real.exp (-x)) ≤ Real.exp (-x) * x :=
            mul_le_mul (le_trans h3 h4) h1 hpos (Real.exp_pos _).le
        _ = x * Real.exp (-x) := by ring


lemma fconc_le (T R1 r : ℝ) (hT : 0 < T) (hr : 0 ≤ r) (hrR : r ≤ R1) :
    CouplingHMC.Exact.fConc T⁻¹ R1 r = T * (1 - Real.exp (-(T⁻¹ * r))) := by
  have hTi : 0 < T⁻¹ := inv_pos.mpr hT
  unfold CouplingHMC.Exact.fConc
  have hcongr : Set.EqOn (fun s => Real.exp (-(T⁻¹ * min s R1)))
      (fun s => Real.exp ((-T⁻¹) * s)) (Set.uIcc 0 r) := by
    intro s hs
    rw [Set.uIcc_of_le hr] at hs
    simp only
    rw [min_eq_left (by linarith [hs.2])]
    ring_nf
  rw [intervalIntegral.integral_congr hcongr,
    intervalIntegral.integral_comp_mul_left (fun s => Real.exp s) (neg_ne_zero.mpr hTi.ne'),
    integral_exp]
  simp only [mul_zero, Real.exp_zero, smul_eq_mul]
  field_simp
  ring_nf

end Aux_CHMC119

open CouplingHMC.Exact in
theorem solution (K T ℛ : ℝ) (hT : 0 < T) (hℛ : 0 ≤ ℛ) (hK : 0 < K) :
    (∀ r : ℝ, 0 < r →
      max 1 (aC T * R1C T ℛ) * Real.exp (-(aC T * R1C T ℛ)) * fConc (aC T) (R1C T ℛ) r ≤
        r * Real.exp (-(aC T * min r (R1C T ℛ)))) ∧
    1 / 4 * K * T ^ 2 * (5 / 2) * (1 + ℛ / T) * Real.exp (-(5 / 2)) *
        Real.exp (-(5 * ℛ / (2 * T))) ≤
      1 / 4 * K * T ^ 2 * max 1 (aC T * R1C T ℛ) * Real.exp (-(aC T * R1C T ℛ)) ∧
    1 / 20 * K * T ^ 2 * (1 + ℛ / T) * Real.exp (-(5 * ℛ / (2 * T))) <
      1 / 4 * K * T ^ 2 * (5 / 2) * (1 + ℛ / T) * Real.exp (-(5 / 2)) *
        Real.exp (-(5 * ℛ / (2 * T))) := by
  have haC : aC T = T⁻¹ := rfl
  have hTi : 0 < T⁻¹ := inv_pos.mpr hT
  set R1 := R1C T ℛ with hR1
  have hR1pos : 0 < R1 := by rw [hR1]; unfold R1C; positivity
  set y := T⁻¹ * R1 with hydef
  have hyv : y = 5 / 2 * (1 + ℛ / T) := by
    rw [hydef, hR1]; unfold R1C; field_simp; ring
  have hy1 : 5 / 2 ≤ y := by
    rw [hyv]; have : 0 ≤ ℛ / T := div_nonneg hℛ hT.le; linarith
  have hmax : max 1 y = y := max_eq_right (by linarith)
  refine ⟨fun r hr => ?_, ?_, ?_⟩
  · rw [haC, ← hydef, hmax]
    rcases le_total r R1 with hrR | hrR
    · rw [Aux_CHMC119.fconc_le T R1 r hT hr.le hrR, min_eq_left hrR]
      have hc := Aux_CHMC119.core (T⁻¹ * r) y (by positivity)
        (by rw [hydef]; exact mul_le_mul_of_nonneg_left hrR hTi.le)
      rw [max_eq_right (by linarith)] at hc
      calc y * Real.exp (-y) * (T * (1 - Real.exp (-(T⁻¹ * r))))
          = y * Real.exp (-y) * (1 - Real.exp (-(T⁻¹ * r))) * T := by ring
        _ ≤ T⁻¹ * r * Real.exp (-(T⁻¹ * r)) * T := mul_le_mul_of_nonneg_right hc hT.le
        _ = r * Real.exp (-(T⁻¹ * r)) := by field_simp
    · -- split the integral at R1
      have hcont : Continuous (fun s => Real.exp (-(T⁻¹ * min s R1))) := by fun_prop
      have hsplit : fConc T⁻¹ R1 r = fConc T⁻¹ R1 R1 + (r - R1) * Real.exp (-y) := by
        unfold fConc
        rw [← intervalIntegral.integral_add_adjacent_intervals
          (hcont.intervalIntegrable 0 R1) (hcont.intervalIntegrable R1 r)]
        congr 1
        have hc2 : Set.EqOn (fun s => Real.exp (-(T⁻¹ * min s R1))) (fun _ => Real.exp (-y))
            (Set.uIcc R1 r) := by
          intro s hs
          rw [Set.uIcc_of_le hrR] at hs
          simp only
          rw [min_eq_right hs.1, hydef]
        rw [intervalIntegral.integral_congr hc2, intervalIntegral.integral_const, smul_eq_mul]
      rw [hsplit, Aux_CHMC119.fconc_le T R1 R1 hT hR1pos.le le_rfl, ← hydef, min_eq_right hrR,
        ← hydef]
      have hE : 0 < Real.exp (-y) := Real.exp_pos _
      have hye : y * Real.exp (-y) ≤ 1 := by
        have h1 := Real.add_one_le_exp y
        have h2 : Real.exp y * Real.exp (-y) = 1 := by rw [← Real.exp_add]; simp
        nlinarith
      set x := T⁻¹ * r with hx
      have hxy : y ≤ x := by rw [hx, hydef]; exact mul_le_mul_of_nonneg_left hrR hTi.le
      have hr' : r = T * x := by rw [hx]; field_simp
      have hR1' : R1 = T * y := by rw [hydef]; field_simp
      rw [hr', hR1']
      have key : y * (1 - Real.exp (-y)) + y * (x - y) * Real.exp (-y) ≤ x := by
        rcases le_total 1 (x - y) with hd | hd
        · nlinarith
        · nlinarith
      have : y * Real.exp (-y) * (T * (1 - Real.exp (-y)) + (T * x - T * y) * Real.exp (-y)) =
          T * Real.exp (-y) * (y * (1 - Real.exp (-y)) + y * (x - y) * Real.exp (-y)) := by ring
      rw [this]
      have : T * x * Real.exp (-y) = T * Real.exp (-y) * x := by ring
      rw [this]
      exact mul_le_mul_of_nonneg_left key (by positivity)
  · apply le_of_eq
    rw [haC, ← hydef, hmax, hyv]
    have : -(5 / 2 * (1 + ℛ / T)) = -(5 / 2) + -(5 * ℛ / (2 * T)) := by field_simp; ring
    rw [this, Real.exp_add]
    ring
  · have h1 : Real.exp (5 / 2) < 25 / 2 := by
      have hsq : Real.exp (5 / 2) ^ 2 = Real.exp 1 ^ 5 := by
        rw [← Real.exp_nat_mul, ← Real.exp_nat_mul]; norm_num
      have h2 := Real.exp_one_lt_d9
      have h3 : Real.exp 1 ^ 5 < (2.7182818286 : ℝ) ^ 5 :=
        pow_lt_pow_left₀ h2 (Real.exp_pos 1).le (by norm_num)
      have h4 : (2.7182818286 : ℝ) ^ 5 < (25 / 2) ^ 2 := by norm_num
      nlinarith [Real.exp_pos (5 / 2)]
    have h2 : (2 / 25 : ℝ) < Real.exp (-(5 / 2)) := by
      rw [Real.exp_neg, lt_inv_comm₀ (by norm_num) (Real.exp_pos _)]
      linarith
    have hpos : 0 < K * T ^ 2 * (1 + ℛ / T) * Real.exp (-(5 * ℛ / (2 * T))) := by positivity
    nlinarith
