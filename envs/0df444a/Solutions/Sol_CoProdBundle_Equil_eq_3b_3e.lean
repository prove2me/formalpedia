-- Prove2me | solution 1 for CoProdBundle.Equil.eq_3b_3e
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-20T16:48:43.968073+00:00
-- url     : https://prove2.me/submissions/13242c80-7e83-4066-841f-00ef5423f200

import Mathlib
import Definitions.Def_CoProdBundle_Equil_Setting

set_option autoImplicit false
open CoProdBundle.Equil

lemma rpow32_eq {x : ℝ} (hx : 0 ≤ x) : x ^ (3/2 : ℝ) = (Real.sqrt x) ^ 3 := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hx]; norm_num

lemma surplus_le (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 ≤ Q) (P : ℝ) :
    surplus A b w θ Q P ≤ (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ) := by
  have hq : 0 ≤ Q ^ θ := Real.rpow_nonneg hQ θ
  have hM : 0 ≤ (A - b * w) / 3 * Q ^ θ := by positivity
  rw [rpow32_eq hM]
  set t := Real.sqrt ((A - b * w) / 3 * Q ^ θ) with ht
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have ht2 : t ^ 2 = (A - b * w) / 3 * Q ^ θ := Real.sq_sqrt hM
  unfold surplus demand
  set u := A * Q ^ θ - b * P with hu
  by_cases hu0 : u ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos hu0]
    have : 0 ≤ (2 / b) * t ^ 3 := by positivity
    simpa using this
  · push_neg at hu0
    set s := Real.sqrt u with hs
    have hs0 : 0 ≤ s := Real.sqrt_nonneg _
    have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
    have hP : b * P = A * Q ^ θ - s ^ 2 := by rw [hs2, hu]; ring
    rw [div_mul_eq_mul_div, le_div_iff₀ hb]
    have e : (P - w * Q ^ θ) * s * b = (3 * t ^ 2 - s ^ 2) * s := by
      linear_combination s * hP - 3 * s * ht2
    have e2 : (P - w * Q ^ θ) * s * b = (P - w * Q ^ θ) * s * b := rfl
    nlinarith [mul_nonneg (sq_nonneg (t - s)) (by linarith : 0 ≤ 2 * t + s)]

lemma Pstar_demand (A b w θ Q : ℝ) (hb : 0 < b) (hQ : 0 ≤ Q) :
    demand A b θ (Pstar A b w θ Q) Q = Real.sqrt ((A - b * w) / 3 * Q ^ θ) := by
  unfold demand Pstar
  congr 1
  field_simp
  ring

lemma surplus_Pstar (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 ≤ Q) :
    surplus A b w θ Q (Pstar A b w θ Q) = (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ) := by
  have hq : 0 ≤ Q ^ θ := Real.rpow_nonneg hQ θ
  have hM : 0 ≤ (A - b * w) / 3 * Q ^ θ := by positivity
  rw [rpow32_eq hM]
  unfold surplus
  rw [Pstar_demand A b w θ Q hb hQ]
  set t := Real.sqrt ((A - b * w) / 3 * Q ^ θ) with ht
  have ht2 : t ^ 2 = (A - b * w) / 3 * Q ^ θ := Real.sq_sqrt hM
  unfold Pstar
  field_simp
  linear_combination (-6 * t) * ht2

lemma Pstar_unique (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 < Q) (P : ℝ)
    (hP : surplus A b w θ Q P = (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ)) :
    P = Pstar A b w θ Q := by
  have hq : 0 < Q ^ θ := Real.rpow_pos_of_pos hQ θ
  have hM : 0 < (A - b * w) / 3 * Q ^ θ := by positivity
  rw [rpow32_eq hM.le] at hP
  set t := Real.sqrt ((A - b * w) / 3 * Q ^ θ) with ht
  have ht0 : 0 < t := Real.sqrt_pos.mpr hM
  have ht2 : t ^ 2 = (A - b * w) / 3 * Q ^ θ := Real.sq_sqrt hM.le
  unfold surplus demand at hP
  set u := A * Q ^ θ - b * P with hu
  by_cases hu0 : u ≤ 0
  · rw [Real.sqrt_eq_zero_of_nonpos hu0] at hP
    simp at hP
    exfalso
    rcases hP with h | h
    · exact hb.ne' h
    · exact ht0.ne' h
  · push_neg at hu0
    set s := Real.sqrt u with hs
    have hs0 : 0 < s := Real.sqrt_pos.mpr hu0
    have hs2 : s ^ 2 = u := Real.sq_sqrt hu0.le
    have hPb : b * P = A * Q ^ θ - s ^ 2 := by rw [hs2, hu]; ring
    rw [div_mul_eq_mul_div, eq_div_iff hb.ne'] at hP
    have e : (P - w * Q ^ θ) * s * b = (3 * t ^ 2 - s ^ 2) * s := by
      linear_combination s * hPb - 3 * s * ht2
    have h3 : (t - s) ^ 2 * (2 * t + s) = 0 := by nlinarith
    have h4 : (t - s) ^ 2 = 0 := by
      rcases mul_eq_zero.mp h3 with h | h
      · exact h
      · linarith
    have h5 : s = t := by nlinarith [sq_nonneg (t - s)]
    have h6 : u = (A - b * w) / 3 * Q ^ θ := by rw [← hs2, h5, ht2]
    unfold Pstar
    rw [hu] at h6
    field_simp
    nlinarith [h6]

lemma S_eq (A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hQ : 0 ≤ Q) :
    S A b w θ Q = (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ) := by
  unfold S
  apply le_antisymm
  · exact ciSup_le fun P => surplus_le A b w θ Q hb hAw hQ P
  · refine le_ciSup_of_le ⟨(2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ), ?_⟩
      (Pstar A b w θ Q) (surplus_Pstar A b w θ Q hb hAw hQ).ge
    rintro _ ⟨P, rfl⟩
    exact surplus_le A b w θ Q hb hAw hQ P

lemma pstar_optimal (γ A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hγ1 : γ < 1)
    (hQ : 0 ≤ Q) : IsRetailerOptimal γ A b w θ Q (Pstar A b w θ Q) := by
  intro P'
  unfold retailerProfit
  apply mul_le_mul_of_nonneg_left _ (by linarith)
  rw [surplus_Pstar A b w θ Q hb hAw hQ]
  exact surplus_le A b w θ Q hb hAw hQ P'

lemma retailer_unique (γ A b w θ Q : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hγ1 : γ < 1)
    (hQ : 0 < Q) (P : ℝ) (hP : IsRetailerOptimal γ A b w θ Q P) : P = Pstar A b w θ Q := by
  have h := hP (Pstar A b w θ Q)
  unfold retailerProfit at h
  have h2 : surplus A b w θ Q (Pstar A b w θ Q) ≤ surplus A b w θ Q P :=
    le_of_mul_le_mul_left h (by linarith)
  apply Pstar_unique A b w θ Q hb hAw hQ
  apply le_antisymm (surplus_le A b w θ Q hb hAw hQ.le P)
  rw [← surplus_Pstar A b w θ Q hb hAw hQ.le]
  exact h2

theorem solution (A b w θ γ : ℝ) (hb : 0 < b) (hAw : 0 < A - b * w) (hθ0 : 0 < θ)
    (hθ1 : θ < 2 / 3) (hγ0 : 0 < γ) (hγ1 : γ < 1) :
    (∀ Q : ℝ, 0 < Q →
      (IsRetailerOptimal γ A b w θ Q (Pstar A b w θ Q) ∧
        ∀ P : ℝ, IsRetailerOptimal γ A b w θ Q P → P = Pstar A b w θ Q) ∧
      demand A b θ (Pstar A b w θ Q) Q = Real.sqrt ((A - b * w) / 3 * Q ^ θ) ∧
      retailerProfit γ A b w θ Q (Pstar A b w θ Q) =
        (2 / b) * (1 - γ) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ)) ∧
    ∀ Q : ℝ, 0 ≤ Q → S A b w θ Q = (2 / b) * ((A - b * w) / 3 * Q ^ θ) ^ (3 / 2 : ℝ) := by
  refine ⟨fun Q hQ => ⟨⟨pstar_optimal γ A b w θ Q hb hAw hγ1 hQ.le,
    fun P hP => retailer_unique γ A b w θ Q hb hAw hγ1 hQ P hP⟩,
    Pstar_demand A b w θ Q hb hQ.le, ?_⟩, fun Q hQ => S_eq A b w θ Q hb hAw hQ⟩
  unfold retailerProfit
  rw [surplus_Pstar A b w θ Q hb hAw hQ.le]
  ring
