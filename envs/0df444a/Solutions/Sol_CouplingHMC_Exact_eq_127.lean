-- Prove2me | solution 1 for CouplingHMC.Exact.eq_127
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-10-26T17:41:33.7716+00:00
-- url     : https://prove2.me/submissions/0df688f0-4d4f-4a45-a06a-a4cacfeaab67

import Mathlib
import Definitions.Def_CouplingHMC_Exact_Setting
open MeasureTheory ProbabilityTheory
open scoped ENNReal InnerProductSpace

namespace Aux_CHMC127

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

end Aux_CHMC127

open CouplingHMC.Exact in
theorem solution (T ℛ : ℝ) (hT : 0 < T) (hℛ : 0 ≤ ℛ) :
    (∀ r : ℝ, 0 < r → r ≤ 2 * ℛ →
      max 1 (2 * aC T * ℛ) * Real.exp (-(2 * aC T * ℛ)) * fConc (aC T) (R1C T ℛ) r ≤
        r * Real.exp (-(aC T * r))) ∧
    (0 < ℛ →
      1 / 5 * gammaC T ℛ * T * max 1 (2 * aC T * ℛ) * Real.exp (-(2 * aC T * ℛ)) =
        1 / 5 * min 1 (T / (4 * ℛ)) * max 1 (2 * ℛ / T) * Real.exp (-(2 * ℛ / T))) ∧
    (ℛ = 0 →
      1 / 5 * gammaC T ℛ * T * max 1 (2 * aC T * ℛ) * Real.exp (-(2 * aC T * ℛ)) = 1 / 5) ∧
    1 / 10 * Real.exp (-(2 * ℛ / T)) ≤
      1 / 5 * gammaC T ℛ * T * max 1 (2 * aC T * ℛ) * Real.exp (-(2 * aC T * ℛ)) := by
  have haC : aC T = T⁻¹ := rfl
  have hy : 2 * aC T * ℛ = 2 * ℛ / T := by rw [haC]; field_simp
  have hTi : 0 < T⁻¹ := inv_pos.mpr hT
  refine ⟨fun r hr hr2 => ?_, fun hpos => ?_, fun h0 => ?_, ?_⟩
  · -- compute fConc
    have hR1 : r < R1C T ℛ := by unfold R1C; linarith
    have hf : fConc (aC T) (R1C T ℛ) r = T * (1 - Real.exp (-(T⁻¹ * r))) := by
      unfold fConc
      have hcongr : Set.EqOn (fun s => Real.exp (-(aC T * min s (R1C T ℛ))))
          (fun s => Real.exp ((-T⁻¹) * s)) (Set.uIcc 0 r) := by
        intro s hs
        rw [Set.uIcc_of_le hr.le] at hs
        simp only
        rw [min_eq_left (by linarith [hs.2]), haC]
        ring_nf
      rw [intervalIntegral.integral_congr hcongr,
        intervalIntegral.integral_comp_mul_left (fun s => Real.exp s) (neg_ne_zero.mpr hTi.ne'),
        integral_exp]
      simp only [mul_zero, Real.exp_zero, smul_eq_mul]
      field_simp
      ring_nf
    rw [hf, haC]
    have hc := Aux_CHMC127.core (T⁻¹ * r) (2 * T⁻¹ * ℛ) (by positivity)
      (by nlinarith)
    have e : T⁻¹ * r * Real.exp (-(T⁻¹ * r)) * T = r * Real.exp (-(T⁻¹ * r)) := by
      field_simp
    calc max 1 (2 * T⁻¹ * ℛ) * Real.exp (-(2 * T⁻¹ * ℛ)) * (T * (1 - Real.exp (-(T⁻¹ * r))))
        = max 1 (2 * T⁻¹ * ℛ) * Real.exp (-(2 * T⁻¹ * ℛ)) * (1 - Real.exp (-(T⁻¹ * r))) * T := by
          ring
      _ ≤ T⁻¹ * r * Real.exp (-(T⁻¹ * r)) * T := mul_le_mul_of_nonneg_right hc hT.le
      _ = r * Real.exp (-(T⁻¹ * r)) := e
  · have hg : gammaC T ℛ = min T⁻¹ (ℛ⁻¹ / 4) := by
      unfold gammaC; rw [if_neg hpos.ne']
    rw [hg, hy]
    have hm : min T⁻¹ (ℛ⁻¹ / 4) * T = min 1 (T / (4 * ℛ)) := by
      rw [min_mul_of_nonneg _ _ hT.le, inv_mul_cancel₀ hT.ne']
      congr 1
      field_simp
    calc 1 / 5 * min T⁻¹ (ℛ⁻¹ / 4) * T * max 1 (2 * ℛ / T) * Real.exp (-(2 * ℛ / T))
        = 1 / 5 * (min T⁻¹ (ℛ⁻¹ / 4) * T) * max 1 (2 * ℛ / T) * Real.exp (-(2 * ℛ / T)) := by ring
      _ = _ := by rw [hm]
  · have hg : gammaC T ℛ = T⁻¹ := by unfold gammaC; rw [if_pos h0]
    rw [hg, h0, haC]
    simp only [mul_zero, max_eq_left zero_le_one, neg_zero, Real.exp_zero, mul_one]
    field_simp
  · rw [hy]
    have hE : 0 < Real.exp (-(2 * ℛ / T)) := Real.exp_pos _
    have key : 1 / 2 ≤ gammaC T ℛ * T * max 1 (2 * ℛ / T) := by
      by_cases h0 : ℛ = 0
      · have hg : gammaC T ℛ = T⁻¹ := by unfold gammaC; rw [if_pos h0]
        rw [hg, inv_mul_cancel₀ hT.ne']
        have := le_max_left 1 (2 * ℛ / T)
        linarith
      · have hpos : 0 < ℛ := lt_of_le_of_ne hℛ (Ne.symm h0)
        have hg : gammaC T ℛ = min T⁻¹ (ℛ⁻¹ / 4) := by unfold gammaC; rw [if_neg h0]
        rw [hg]
        have hm : min T⁻¹ (ℛ⁻¹ / 4) * T = min 1 (T / (4 * ℛ)) := by
          rw [min_mul_of_nonneg _ _ hT.le, inv_mul_cancel₀ hT.ne']
          congr 1
          field_simp
        rw [hm]
        rcases le_total 1 (T / (4 * ℛ)) with h | h
        · rw [min_eq_left h]
          have := le_max_left 1 (2 * ℛ / T)
          linarith
        · rw [min_eq_right h]
          have h2 : 2 * ℛ / T ≤ max 1 (2 * ℛ / T) := le_max_right _ _
          have h3 : T / (4 * ℛ) * (2 * ℛ / T) = 1 / 2 := by field_simp; ring
          have h4 : 0 ≤ T / (4 * ℛ) := by positivity
          nlinarith [mul_le_mul_of_nonneg_left h2 h4]
    nlinarith
