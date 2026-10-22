-- Prove2me | solution 1 for DigitalPrivacy.Strategy.theorem_1
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-21T20:29:38.768614+00:00
-- url     : https://prove2.me/submissions/08185fcd-b276-48ee-80b5-ff2252f93bf3

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting

set_option autoImplicit false

namespace DPHelp
open DigitalPrivacy.Strategy

/-- reduced one-dimensional objective: `sqrt((1+ρξ)(1-P+Pξ)) - sqrt(ψ) ξ` -/
noncomputable def gv (ρ ψ P ξ : ℝ) : ℝ := √((1 + ρ * ξ) * (1 - P + P * ξ)) - √ψ * ξ

noncomputable def rp (ρ ψ P : ℝ) : ℝ := (√ψ - √(ψ - P * ρ)) / ρ
noncomputable def rn (ρ ψ P : ℝ) : ℝ := (√ψ + √(ψ - P * ρ)) / ρ
noncomputable def Kf (r P M : ℝ) : ℝ := (r ^ 2 - (1 - P)) * (r ^ 2 + (1 - P)) / (4 * r ^ 2 * M)

lemma sq_le_imp {x y : ℝ} (hy : 0 ≤ y) (h : x ^ 2 ≤ y ^ 2) : x ≤ y := by
  by_contra hc
  push_neg at hc
  nlinarith

lemma tangent {u v t : ℝ} (hu : 0 ≤ u) (hv : 0 ≤ v) (ht : 0 < t) :
    2 * t * √(u * v) ≤ u * t ^ 2 + v := by
  rw [Real.sqrt_mul hu]
  have hu' := Real.sq_sqrt hu
  have hv' := Real.sq_sqrt hv
  have key : u * t ^ 2 + v - 2 * t * (√u * √v) = (t * √u - √v) ^ 2 := by
    linear_combination (-(t ^ 2)) * hu' - hv'
  nlinarith [sq_nonneg (t * √u - √v)]

lemma profit_eq (β ρ ψ P ξ C : ℝ) (hξ : ξ ≠ 0) (hD : C * (1 - β) + ξ ^ 2 ≠ 0) :
    profit β ρ ψ P ξ C =
      C * ((1 + ρ * ξ) * (1 - P + P * ξ) - ψ * (C * (1 - β) + ξ ^ 2)) /
        (C * (1 - β) + ξ ^ 2) := by
  unfold profit abar
  rw [if_neg hξ]
  field_simp

lemma profit_zero (β ρ ψ P C : ℝ) :
    profit β ρ ψ P 0 C = (1 - P) * (1 / (1 - β)) - ψ * C := by
  unfold profit abar
  rw [if_pos rfl]
  ring

lemma alg_bound (k C ξ A S q ψ : ℝ) (hk : 0 < k) (hC : 0 ≤ C) (hξ : 0 < ξ) (hS0 : 0 ≤ S)
    (hS2 : S ^ 2 = A) (hq0 : 0 < q) (hq2 : q ^ 2 = ψ) :
    k * (C * (A - ψ * (C * k + ξ ^ 2)) / (C * k + ξ ^ 2)) ≤ (max (S - q * ξ) 0) ^ 2 := by
  subst hS2 hq2
  have hD : 0 < C * k + ξ ^ 2 := by positivity
  rw [← mul_div_assoc, div_le_iff₀ hD]
  rcases le_or_gt 0 (S - q * ξ) with h | h
  · rw [max_eq_left h]
    nlinarith [sq_nonneg (ξ * S - q * (C * k + ξ ^ 2))]
  · rw [max_eq_right h.le]
    have h1 : S ^ 2 ≤ q ^ 2 * ξ ^ 2 := by
      nlinarith [mul_self_le_mul_self hS0 (le_of_lt (by linarith : S < q * ξ))]
    have h2 : 0 ≤ C * k := mul_nonneg hC hk.le
    have h3 : S ^ 2 ≤ q ^ 2 * (C * k + ξ ^ 2) := by nlinarith [mul_nonneg (sq_nonneg q) h2]
    nlinarith [mul_nonneg (mul_nonneg hk.le hC) (sub_nonneg.mpr h3)]

lemma alg_value (k ξ S q ψ A : ℝ) (hk : 0 < k) (hξ : 0 < ξ) (hS : 0 < S) (hq : 0 < q)
    (hq2 : q ^ 2 = ψ) (hS2 : S ^ 2 = A) :
    k * ((ξ / k * (-ξ + S / q)) * (A - ψ * ((ξ / k * (-ξ + S / q)) * k + ξ ^ 2)) /
      ((ξ / k * (-ξ + S / q)) * k + ξ ^ 2)) = (S - q * ξ) ^ 2 := by
  subst hq2 hS2
  have hD : (ξ / k * (-ξ + S / q)) * k + ξ ^ 2 = ξ * S / q := by
    field_simp
    ring
  rw [hD]
  field_simp
  ring

lemma sqrt_rw (ψ ρ P ξ : ℝ) (hψ : 0 < ψ) :
    √((1 / ψ) * (1 + ρ * ξ) * (1 - P * (1 - ξ))) = √((1 + ρ * ξ) * (1 - P + P * ξ)) / √ψ := by
  rw [show (1 / ψ) * (1 + ρ * ξ) * (1 - P * (1 - ξ)) = ((1 + ρ * ξ) * (1 - P + P * ξ)) / ψ by
    ring]
  rw [Real.sqrt_div' _ hψ.le]

lemma gv_one (ρ ψ P : ℝ) : gv ρ ψ P 1 = √(1 + ρ) - √ψ := by
  unfold gv
  rw [show (1 + ρ * 1) * (1 - P + P * 1) = 1 + ρ by ring, mul_one]

lemma gv_zero (ρ ψ P : ℝ) : gv ρ ψ P 0 = √(1 - P) := by
  unfold gv
  simp

lemma end1 (ρ ψ P ξ : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hP1 : P ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (h : 2 * √ψ * √(1 + ρ) ≤ ρ + P * (1 + ρ)) :
    gv ρ ψ P ξ ≤ gv ρ ψ P 1 := by
  rw [gv_one]
  unfold gv
  have hu : 0 ≤ 1 + ρ * ξ := by positivity
  have hv : 0 ≤ 1 - P + P * ξ := by nlinarith
  have hw0 : 0 < √(1 + ρ) := Real.sqrt_pos.mpr (by linarith)
  have hw2 : √(1 + ρ) ^ 2 = 1 + ρ := Real.sq_sqrt (by linarith)
  have ht : 2 * √(1 + ρ) * √((1 + ρ * ξ) * (1 - P + P * ξ)) ≤
      (1 - P + P * ξ) * √(1 + ρ) ^ 2 + (1 + ρ * ξ) := by
    have := tangent hv hu hw0
    rwa [mul_comm (1 - P + P * ξ)] at this
  rw [hw2] at ht
  have h2 : 2 * √ψ * √(1 + ρ) * (1 - ξ) ≤ (ρ + P * (1 + ρ)) * (1 - ξ) :=
    mul_le_mul_of_nonneg_right h (by linarith)
  have : 2 * √(1 + ρ) * (√((1 + ρ * ξ) * (1 - P + P * ξ)) - √ψ * ξ) ≤
      2 * √(1 + ρ) * (√(1 + ρ) - √ψ) := by
    nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

lemma end0 (ρ ψ P ξ : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hP1 : P < 1)
    (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (h : (1 - P) * ρ + P ≤ 2 * √ψ * √(1 - P)) :
    gv ρ ψ P ξ ≤ gv ρ ψ P 0 := by
  rw [gv_zero]
  unfold gv
  have hu : 0 ≤ 1 + ρ * ξ := by positivity
  have hv : 0 ≤ 1 - P + P * ξ := by nlinarith
  have hz0 : 0 < √(1 - P) := Real.sqrt_pos.mpr (by linarith)
  have hz2 : √(1 - P) ^ 2 = 1 - P := Real.sq_sqrt (by linarith)
  have ht := tangent hu hv hz0
  rw [hz2] at ht
  have h2 : ξ * ((1 - P) * ρ + P) ≤ ξ * (2 * √ψ * √(1 - P)) := mul_le_mul_of_nonneg_left h hξ0
  have : 2 * √(1 - P) * (√((1 + ρ * ξ) * (1 - P + P * ξ)) - √ψ * ξ) ≤
      2 * √(1 - P) * √(1 - P) := by
    nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

lemma interior (ρ ψ P ξ ξI r : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hP1 : P ≤ 1)
    (hξ0 : 0 ≤ ξ) (hξI : 0 ≤ ξI) (hr : 0 < r)
    (hq : ρ * r ^ 2 - 2 * √ψ * r + P = 0)
    (hv : 1 - P + P * ξI = r ^ 2 * (1 + ρ * ξI)) :
    gv ρ ψ P ξ ≤ gv ρ ψ P ξI := by
  have hu : 0 ≤ 1 + ρ * ξ := by positivity
  have hvv : 0 ≤ 1 - P + P * ξ := by nlinarith
  have huI : 0 ≤ 1 + ρ * ξI := by positivity
  have hsI : √((1 + ρ * ξI) * (1 - P + P * ξI)) = r * (1 + ρ * ξI) := by
    rw [hv, show (1 + ρ * ξI) * (r ^ 2 * (1 + ρ * ξI)) = (r * (1 + ρ * ξI)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  unfold gv
  rw [hsI]
  have ht := tangent hu hvv hr
  have e1 : 2 * r * (r * (1 + ρ * ξI) - √ψ * ξI) = r ^ 2 + 1 - P := by
    linear_combination (-1) * hv + ξI * hq
  have h0 : ξ * (ρ * r ^ 2 - 2 * √ψ * r + P) = 0 := by rw [hq]; ring
  have : 2 * r * (√((1 + ρ * ξ) * (1 - P + P * ξ)) - √ψ * ξ) ≤
      2 * r * (r * (1 + ρ * ξI) - √ψ * ξI) := by
    rw [e1]
    nlinarith
  exact le_of_mul_le_mul_left this (by positivity)

lemma xiI_key (ρ ψ P x : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hD : P * ρ < ψ) :
    ∃ T : ℝ, 0 ≤ T ∧ 2 * (xiI ρ ψ P - x) * (((1 - P) * ρ + P + 2 * P * ρ * x) + T) *
      (ψ - P * ρ) = (P - (1 - P) * ρ) ^ 2 - 4 * (ψ - P * ρ) * ((1 + ρ * x) * (1 - P + P * x)) := by
  have hψ0 : 0 < ψ := by nlinarith [mul_pos hP0 hρ0]
  have hDp : 0 < ψ - P * ρ := by linarith
  refine ⟨|P - (1 - P) * ρ| * √(ψ / (ψ - P * ρ)), by positivity, ?_⟩
  have hT2 : (|P - (1 - P) * ρ| * √(ψ / (ψ - P * ρ))) ^ 2 * (ψ - P * ρ) =
      (P - (1 - P) * ρ) ^ 2 * ψ := by
    rw [mul_pow, sq_abs, Real.sq_sqrt (div_nonneg hψ0.le hDp.le), mul_assoc,
      div_mul_cancel₀ _ hDp.ne']
  have hxi2 : 2 * P * ρ * xiI ρ ψ P =
      -(1 - P) * ρ - P + |P - (1 - P) * ρ| * √(ψ / (ψ - P * ρ)) := by
    unfold xiI
    rw [← mul_assoc, mul_one_div_cancel (by positivity), one_mul]
  have key : P * ρ * (2 * (xiI ρ ψ P - x) * (((1 - P) * ρ + P + 2 * P * ρ * x) +
      |P - (1 - P) * ρ| * √(ψ / (ψ - P * ρ))) * (ψ - P * ρ)) =
      P * ρ * ((P - (1 - P) * ρ) ^ 2 - 4 * (ψ - P * ρ) * ((1 + ρ * x) * (1 - P + P * x))) := by
    linear_combination ((((1 - P) * ρ + P + 2 * P * ρ * x) +
      |P - (1 - P) * ρ| * √(ψ / (ψ - P * ρ))) * (ψ - P * ρ)) * hxi2 + hT2
  exact mul_left_cancel₀ (by positivity) key

lemma xiI_le_iff (ρ ψ P x : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hP1 : P ≤ 1) (hD : P * ρ < ψ)
    (hx : 0 ≤ x) :
    (x ≤ xiI ρ ψ P ↔
      4 * (ψ - P * ρ) * ((1 + ρ * x) * (1 - P + P * x)) ≤ (P - (1 - P) * ρ) ^ 2) ∧
    (x < xiI ρ ψ P ↔
      4 * (ψ - P * ρ) * ((1 + ρ * x) * (1 - P + P * x)) < (P - (1 - P) * ρ) ^ 2) := by
  obtain ⟨T, hT, hkey⟩ := xiI_key ρ ψ P x hρ0 hP0 hD
  have hA : 0 < (1 - P) * ρ + P + 2 * P * ρ * x := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hP1) hρ0.le, mul_nonneg (mul_nonneg hP0.le hρ0.le) hx]
  have hpos : 0 < (((1 - P) * ρ + P + 2 * P * ρ * x) + T) * (ψ - P * ρ) := by
    apply mul_pos
    · linarith
    · linarith
  have hk2 : 2 * (xiI ρ ψ P - x) * ((((1 - P) * ρ + P + 2 * P * ρ * x) + T) * (ψ - P * ρ)) =
      (P - (1 - P) * ρ) ^ 2 - 4 * (ψ - P * ρ) * ((1 + ρ * x) * (1 - P + P * x)) := by
    rw [← hkey]; ring
  constructor
  · constructor
    · intro h
      nlinarith [mul_nonneg (sub_nonneg.mpr h) hpos.le]
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [mul_pos (sub_pos.mpr hc) hpos]
  · constructor
    · intro h
      nlinarith [mul_pos (sub_pos.mpr h) hpos]
    · intro h
      by_contra hc
      push_neg at hc
      nlinarith [mul_nonneg (sub_nonneg.mpr hc) hpos.le]

lemma branch_pos (ρ ψ P : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hD : P * ρ < ψ)
    (hd : 0 ≤ P - (1 - P) * ρ) :
    0 < rp ρ ψ P ∧ ρ * rp ρ ψ P ^ 2 - 2 * √ψ * rp ρ ψ P + P = 0 ∧
    √ψ - ρ * rp ρ ψ P = √(ψ - P * ρ) ∧
    2 * rp ρ ψ P * √(ψ - P * ρ) * xiI ρ ψ P = rp ρ ψ P ^ 2 - (1 - P) := by
  have hψ0 : 0 < ψ := by nlinarith [mul_pos hP0 hρ0]
  have hDp : 0 < ψ - P * ρ := by linarith
  have hxi : xiI ρ ψ P = (1 / (2 * P * ρ)) *
      (-(1 - P) * ρ - P + (P - (1 - P) * ρ) * (√ψ / √(ψ - P * ρ))) := by
    unfold xiI
    rw [abs_of_nonneg hd, Real.sqrt_div' _ hDp.le]
  rw [hxi]
  unfold rp
  obtain ⟨q, hq⟩ : ∃ q, q = √ψ := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = √(ψ - P * ρ) := ⟨_, rfl⟩
  rw [← hq, ← hσ]
  have hq0 : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr hψ0
  have hσ0 : 0 < σ := by rw [hσ]; exact Real.sqrt_pos.mpr hDp
  have hq2 : q ^ 2 = ψ := by rw [hq]; exact Real.sq_sqrt hψ0.le
  have hσ2 : σ ^ 2 = ψ - P * ρ := by rw [hσ]; exact Real.sq_sqrt hDp.le
  have hqs : 0 < q ^ 2 - σ ^ 2 := by nlinarith [mul_pos hP0 hρ0]
  have hσq : σ < q := by nlinarith
  have hP : P = (q ^ 2 - σ ^ 2) / ρ := by
    rw [eq_div_iff hρ0.ne']; linarith
  clear hxi hq hσ
  subst hq2
  subst hP
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hσne : σ ≠ 0 := hσ0.ne'
  have hqsne : q ^ 2 - σ ^ 2 ≠ 0 := hqs.ne'
  refine ⟨div_pos (by linarith) hρ0, ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

lemma branch_neg (ρ ψ P : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hD : P * ρ < ψ)
    (hd : P - (1 - P) * ρ < 0) :
    0 < rn ρ ψ P ∧ ρ * rn ρ ψ P ^ 2 - 2 * √ψ * rn ρ ψ P + P = 0 ∧
    √ψ - ρ * rn ρ ψ P = -√(ψ - P * ρ) ∧
    2 * rn ρ ψ P * (-√(ψ - P * ρ)) * xiI ρ ψ P = rn ρ ψ P ^ 2 - (1 - P) := by
  have hψ0 : 0 < ψ := by nlinarith [mul_pos hP0 hρ0]
  have hDp : 0 < ψ - P * ρ := by linarith
  have hxi : xiI ρ ψ P = (1 / (2 * P * ρ)) *
      (-(1 - P) * ρ - P + (-(P - (1 - P) * ρ)) * (√ψ / √(ψ - P * ρ))) := by
    unfold xiI
    rw [abs_of_neg hd, Real.sqrt_div' _ hDp.le]
  rw [hxi]
  unfold rn
  obtain ⟨q, hq⟩ : ∃ q, q = √ψ := ⟨_, rfl⟩
  obtain ⟨σ, hσ⟩ : ∃ σ, σ = √(ψ - P * ρ) := ⟨_, rfl⟩
  rw [← hq, ← hσ]
  have hq0 : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr hψ0
  have hσ0 : 0 < σ := by rw [hσ]; exact Real.sqrt_pos.mpr hDp
  have hq2 : q ^ 2 = ψ := by rw [hq]; exact Real.sq_sqrt hψ0.le
  have hσ2 : σ ^ 2 = ψ - P * ρ := by rw [hσ]; exact Real.sq_sqrt hDp.le
  have hqs : 0 < q ^ 2 - σ ^ 2 := by nlinarith [mul_pos hP0 hρ0]
  have hP : P = (q ^ 2 - σ ^ 2) / ρ := by
    rw [eq_div_iff hρ0.ne']; linarith
  clear hxi hq hσ
  subst hq2
  subst hP
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hσne : σ ≠ 0 := hσ0.ne'
  have hqsne : q ^ 2 - σ ^ 2 ≠ 0 := hqs.ne'
  refine ⟨div_pos (by linarith) hρ0, ?_, ?_, ?_⟩
  · field_simp
    ring
  · field_simp
    ring
  · field_simp
    ring

lemma v_eq (ρ q P r M ξ : ℝ) (hq : ρ * r ^ 2 - 2 * q * r + P = 0) (hM : M = q - ρ * r)
    (hxi : 2 * r * M * ξ = r ^ 2 - (1 - P)) : 1 - P + P * ξ = r ^ 2 * (1 + ρ * ξ) := by
  subst hM
  linear_combination ξ * hq + hxi

lemma xs_cases (ρ ψ P : ℝ) : (ψ ≤ P * ρ ∧ xiStar ρ ψ P = 1) ∨
    (P * ρ < ψ ∧ xiStar ρ ψ P = max 0 (min 1 (xiI ρ ψ P))) := by
  unfold xiStar
  by_cases h : ψ ≤ P * ρ
  · left; exact ⟨h, if_pos h⟩
  · right; exact ⟨not_le.mp h, if_neg h⟩

lemma xs_range (ρ ψ P : ℝ) : 0 ≤ xiStar ρ ψ P ∧ xiStar ρ ψ P ≤ 1 := by
  rcases xs_cases ρ ψ P with ⟨_, h⟩ | ⟨_, h⟩
  · rw [h]; exact ⟨zero_le_one, le_rfl⟩
  · rw [h]; exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma end1_cond (ρ ψ P : ℝ) (hρ0 : 0 < ρ) (hψ : 0 < ψ) (hP0 : 0 < P)
    (h : 4 * ψ * (1 + ρ) ≤ (ρ + P * (1 + ρ)) ^ 2) :
    2 * √ψ * √(1 + ρ) ≤ ρ + P * (1 + ρ) := by
  apply sq_le_imp (by positivity)
  have h1 := Real.sq_sqrt hψ.le
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + ρ by linarith)
  have e : (2 * √ψ * √(1 + ρ)) ^ 2 = 4 * ψ * (1 + ρ) := by
    linear_combination (4 * √(1 + ρ) ^ 2) * h1 + (4 * ψ) * h2
  rw [e]; exact h

lemma end0_cond (ρ ψ P : ℝ) (hψ : 0 < ψ) (hP1 : P < 1)
    (h : ((1 - P) * ρ + P) ^ 2 ≤ 4 * ψ * (1 - P)) :
    (1 - P) * ρ + P ≤ 2 * √ψ * √(1 - P) := by
  apply sq_le_imp (by positivity)
  have h1 := Real.sq_sqrt hψ.le
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 - P by linarith)
  have e : (2 * √ψ * √(1 - P)) ^ 2 = 4 * ψ * (1 - P) := by
    linear_combination (4 * √(1 - P) ^ 2) * h1 + (4 * ψ) * h2
  rw [e]; exact h

lemma conv1 (ρ ψ P : ℝ) :
    4 * (ψ - P * ρ) * ((1 + ρ * 1) * (1 - P + P * 1)) - (P - (1 - P) * ρ) ^ 2 =
      4 * ψ * (1 + ρ) - (ρ + P * (1 + ρ)) ^ 2 := by ring

lemma conv0 (ρ ψ P : ℝ) :
    4 * (ψ - P * ρ) * ((1 + ρ * 0) * (1 - P + P * 0)) - (P - (1 - P) * ρ) ^ 2 =
      4 * ψ * (1 - P) - ((1 - P) * ρ + P) ^ 2 := by ring

lemma gmax (ρ ψ P : ℝ) (hρ0 : 0 < ρ) (hψ : 0 < ψ) (hP0 : 0 < P) (hP1 : P ≤ 1) :
    ∀ ξ, 0 ≤ ξ → ξ ≤ 1 → gv ρ ψ P ξ ≤ gv ρ ψ P (xiStar ρ ψ P) := by
  intro ξ hξ0 hξ1
  rcases xs_cases ρ ψ P with ⟨h, hx⟩ | ⟨h, hx⟩
  · rw [hx]
    apply end1 ρ ψ P ξ hρ0 hP0 hP1 hξ0 hξ1
    apply end1_cond ρ ψ P hρ0 hψ hP0
    nlinarith [sq_nonneg (ρ - P * (1 + ρ)), mul_le_mul_of_nonneg_right h (by linarith : (0:ℝ) ≤ 1 + ρ)]
  · have hk1 := xiI_le_iff ρ ψ P 1 hρ0 hP0 hP1 h zero_le_one
    have hk0 := xiI_le_iff ρ ψ P 0 hρ0 hP0 hP1 h le_rfl
    rcases le_or_gt 1 (xiI ρ ψ P) with h1 | h1
    · rw [hx, min_eq_left h1, max_eq_right zero_le_one]
      apply end1 ρ ψ P ξ hρ0 hP0 hP1 hξ0 hξ1
      apply end1_cond ρ ψ P hρ0 hψ hP0
      have := hk1.1.1 h1
      linarith [conv1 ρ ψ P]
    · rcases le_or_gt (xiI ρ ψ P) 0 with h0 | h0
      · rw [hx, min_eq_right h1.le, max_eq_left h0]
        have h3 : ¬ (4 * (ψ - P * ρ) * ((1 + ρ * 0) * (1 - P + P * 0)) < (P - (1 - P) * ρ) ^ 2) :=
          fun hh => absurd (hk0.2.2 hh) (not_lt.mpr h0)
        push_neg at h3
        have hPlt : P < 1 := by
          rcases lt_or_eq_of_le hP1 with hh | hh
          · exact hh
          · exfalso
            subst hh
            nlinarith
        apply end0 ρ ψ P ξ hρ0 hP0 hPlt hξ0 hξ1
        apply end0_cond ρ ψ P hψ hPlt
        linarith [conv0 ρ ψ P]
      · rw [hx, min_eq_right h1.le, max_eq_right h0.le]
        rcases le_or_gt 0 (P - (1 - P) * ρ) with hd | hd
        · obtain ⟨hr, hq, hM, hxi⟩ := branch_pos ρ ψ P hρ0 hP0 h hd
          have hv := v_eq ρ (√ψ) P _ _ (xiI ρ ψ P) hq hM.symm hxi
          exact interior ρ ψ P ξ (xiI ρ ψ P) _ hρ0 hP0 hP1 hξ0 h0.le hr hq hv
        · obtain ⟨hr, hq, hM, hxi⟩ := branch_neg ρ ψ P hρ0 hP0 h hd
          have hv := v_eq ρ (√ψ) P _ _ (xiI ρ ψ P) hq hM.symm hxi
          exact interior ρ ψ P ξ (xiI ρ ψ P) _ hρ0 hP0 hP1 hξ0 h0.le hr hq hv

lemma g_nonneg (ρ ψ P : ℝ) (hρ0 : 0 < ρ) (hψ : 0 < ψ) (hP0 : 0 < P) (hP1 : P ≤ 1) :
    0 ≤ gv ρ ψ P (xiStar ρ ψ P) := by
  have := gmax ρ ψ P hρ0 hψ hP0 hP1 0 le_rfl zero_le_one
  rw [gv_zero] at this
  exact le_trans (Real.sqrt_nonneg _) this

lemma cstar_eq (β ρ ψ P : ℝ) (hψ : 0 < ψ) :
    CStar β ρ ψ P = xiStar ρ ψ P / (1 - β) *
      (-xiStar ρ ψ P + √((1 + ρ * xiStar ρ ψ P) * (1 - P + P * xiStar ρ ψ P)) / √ψ) := by
  unfold CStar
  rw [sqrt_rw ψ ρ P _ hψ]

lemma main1 (β ρ ψ P : ℝ) (hβ1 : β < 1) (hρ0 : 0 < ρ) (hψ : 0 < ψ)
    (hP0 : 0 < P) (hP1 : P ≤ 1) :
    IsBusinessOpt β ρ ψ P (xiStar ρ ψ P) (CStar β ρ ψ P) ∧ 0 ≤ CStar β ρ ψ P ∧
    CStar β ρ ψ P * (1 - β) * √ψ = xiStar ρ ψ P * gv ρ ψ P (xiStar ρ ψ P) := by
  have hk : 0 < 1 - β := by linarith
  obtain ⟨hx0, hx1⟩ := xs_range ρ ψ P
  have hg := g_nonneg ρ ψ P hρ0 hψ hP0 hP1
  have hq0 : 0 < √ψ := Real.sqrt_pos.mpr hψ
  have hq2 : √ψ ^ 2 = ψ := Real.sq_sqrt hψ.le
  have hce := cstar_eq β ρ ψ P hψ
  -- abbreviations through generalisation
  obtain ⟨ξs, hξs⟩ : ∃ ξs, ξs = xiStar ρ ψ P := ⟨_, rfl⟩
  have hgmax := gmax ρ ψ P hρ0 hψ hP0 hP1
  rw [← hξs] at hx0 hx1 hg hce hgmax ⊢
  have hu : 0 ≤ 1 + ρ * ξs := by positivity
  have hv : 0 ≤ 1 - P + P * ξs := by nlinarith
  have hA0 : 0 ≤ (1 + ρ * ξs) * (1 - P + P * ξs) := mul_nonneg hu hv
  have hS2 : √((1 + ρ * ξs) * (1 - P + P * ξs)) ^ 2 = (1 + ρ * ξs) * (1 - P + P * ξs) :=
    Real.sq_sqrt hA0
  have hg' : 0 ≤ √((1 + ρ * ξs) * (1 - P + P * ξs)) - √ψ * ξs := hg
  -- nonnegativity of C*
  have hC0 : 0 ≤ CStar β ρ ψ P := by
    rw [hce]
    apply mul_nonneg (div_nonneg hx0 hk.le)
    rw [neg_add_eq_sub, sub_nonneg, le_div_iff₀ hq0]
    linarith
  -- the value at the optimum
  have hval : (1 - β) * profit β ρ ψ P ξs (CStar β ρ ψ P) = gv ρ ψ P ξs ^ 2 := by
    rcases eq_or_lt_of_le hx0 with h0 | h0
    · rw [← h0] at hce ⊢
      rw [hce, gv_zero, profit_zero, Real.sq_sqrt (by linarith)]
      field_simp
      ring
    · have hvp : 0 < 1 - P + P * ξs := by nlinarith
      have hS : 0 < √((1 + ρ * ξs) * (1 - P + P * ξs)) :=
        Real.sqrt_pos.mpr (mul_pos (by positivity) hvp)
      have hD : CStar β ρ ψ P * (1 - β) + ξs ^ 2 ≠ 0 := by
        rw [hce]
        have : ξs / (1 - β) * (-ξs + √((1 + ρ * ξs) * (1 - P + P * ξs)) / √ψ) * (1 - β) + ξs ^ 2
            = ξs * √((1 + ρ * ξs) * (1 - P + P * ξs)) / √ψ := by
          field_simp
          ring
        rw [this]
        positivity
      rw [profit_eq β ρ ψ P ξs _ h0.ne' hD, hce]
      unfold gv
      exact alg_value (1 - β) ξs _ (√ψ) ψ _ hk h0 hS hq0 hq2 hS2
  refine ⟨⟨⟨⟨hx0, hx1⟩, hC0⟩, ?_⟩, hC0, ?_⟩
  · intro ξ' C' hF
    obtain ⟨⟨hξ0', hξ1'⟩, hC'⟩ := hF
    have hgξ := hgmax ξ' hξ0' hξ1'
    have hg0 := hgmax 0 le_rfl zero_le_one
    rw [gv_zero] at hg0
    suffices (1 - β) * profit β ρ ψ P ξ' C' ≤ (1 - β) * profit β ρ ψ P ξs (CStar β ρ ψ P) from
      le_of_mul_le_mul_left this hk
    rw [hval]
    rcases eq_or_lt_of_le hξ0' with h0 | h0
    · rw [← h0, profit_zero]
      have e : (1 - β) * ((1 - P) * (1 / (1 - β)) - ψ * C') = (1 - P) - (1 - β) * ψ * C' := by
        field_simp
      rw [e]
      have h1 : 0 ≤ (1 - β) * ψ * C' := by positivity
      have h2 : (1 - P) ≤ gv ρ ψ P ξs ^ 2 := by
        have := mul_self_le_mul_self (Real.sqrt_nonneg _) hg0
        rw [Real.mul_self_sqrt (by linarith)] at this
        nlinarith
      linarith
    · have hu' : 0 ≤ 1 + ρ * ξ' := by positivity
      have hv' : 0 ≤ 1 - P + P * ξ' := by nlinarith
      have hD' : C' * (1 - β) + ξ' ^ 2 ≠ 0 := by positivity
      rw [profit_eq β ρ ψ P ξ' C' h0.ne' hD']
      have hb := alg_bound (1 - β) C' ξ' ((1 + ρ * ξ') * (1 - P + P * ξ'))
        (√((1 + ρ * ξ') * (1 - P + P * ξ'))) (√ψ) ψ hk hC' h0 (Real.sqrt_nonneg _)
        (Real.sq_sqrt (mul_nonneg hu' hv')) hq0 hq2
      refine le_trans hb ?_
      have hm0 : 0 ≤ max (√((1 + ρ * ξ') * (1 - P + P * ξ')) - √ψ * ξ') 0 := le_max_right _ _
      have hm1 : max (√((1 + ρ * ξ') * (1 - P + P * ξ')) - √ψ * ξ') 0 ≤ gv ρ ψ P ξs :=
        max_le hgξ hg
      nlinarith [mul_le_mul hm1 hm1 hm0 hg]
  · rw [hce]
    unfold gv
    field_simp
    ring

lemma conv_gen (ρ ψ P x : ℝ) :
    4 * (ψ - P * ρ) * ((1 + ρ * x) * (1 - P + P * x)) - (P - (1 - P) * ρ) ^ 2 =
      4 * ψ * ((1 + ρ * x) * (1 - P + P * x)) - ((1 - P) * ρ + P + 2 * P * ρ * x) ^ 2 := by ring

lemma sc (ρ ψ P1 P2 x : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hψ : 0 < ψ) (hP1 : 0 < P1)
    (h12 : P1 ≤ P2) (hP2 : P2 ≤ 1) (hx0 : 0 < x) (hx1 : x ≤ 1)
    (h : 4 * ψ * ((1 + ρ * x) * (1 - P1 + P1 * x)) ≤ ((1 - P1) * ρ + P1 + 2 * P1 * ρ * x) ^ 2) :
    4 * ψ * ((1 + ρ * x) * (1 - P2 + P2 * x)) ≤ ((1 - P2) * ρ + P2 + 2 * P2 * ρ * x) ^ 2 := by
  have hu1 : 1 ≤ 1 + ρ * x := by have := mul_nonneg hρ0.le hx0.le; linarith
  have hv1p : 0 < 1 - P1 + P1 * x := by have := mul_pos hP1 hx0; linarith
  have hv2p : 0 < 1 - P2 + P2 * x := by have := mul_pos (lt_of_lt_of_le hP1 h12) hx0; linarith
  have hv12 : 1 - P2 + P2 * x ≤ 1 - P1 + P1 * x := by
    have := mul_nonneg (sub_nonneg.mpr h12) (sub_nonneg.mpr hx1); linarith
  obtain ⟨w1, hw1⟩ : ∃ w, w = √(1 - P1 + P1 * x) := ⟨_, rfl⟩
  obtain ⟨w2, hw2⟩ : ∃ w, w = √(1 - P2 + P2 * x) := ⟨_, rfl⟩
  obtain ⟨su, hsu⟩ : ∃ w, w = √(1 + ρ * x) := ⟨_, rfl⟩
  obtain ⟨q, hq⟩ : ∃ w, w = √ψ := ⟨_, rfl⟩
  have hw1p : 0 < w1 := by rw [hw1]; exact Real.sqrt_pos.mpr hv1p
  have hw2p : 0 < w2 := by rw [hw2]; exact Real.sqrt_pos.mpr hv2p
  have hsup : 0 < su := by rw [hsu]; exact Real.sqrt_pos.mpr (by linarith)
  have hqp : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr hψ
  have hw1s : w1 ^ 2 = 1 - P1 + P1 * x := by rw [hw1]; exact Real.sq_sqrt hv1p.le
  have hw2s : w2 ^ 2 = 1 - P2 + P2 * x := by rw [hw2]; exact Real.sq_sqrt hv2p.le
  have hsus : su ^ 2 = 1 + ρ * x := by rw [hsu]; exact Real.sq_sqrt (by linarith)
  have hqs : q ^ 2 = ψ := by rw [hq]; exact Real.sq_sqrt hψ.le
  have hw21 : w2 ≤ w1 := by rw [hw1, hw2]; exact Real.sqrt_le_sqrt hv12
  have hA1 : (1 - P1) * ρ + P1 + 2 * P1 * ρ * x = ρ * w1 ^ 2 + P1 * (1 + ρ * x) := by
    rw [hw1s]; ring
  have hA2 : (1 - P2) * ρ + P2 + 2 * P2 * ρ * x = ρ * w2 ^ 2 + P2 * (1 + ρ * x) := by
    rw [hw2s]; ring
  have hA1p : 0 ≤ (1 - P1) * ρ + P1 + 2 * P1 * ρ * x := by
    rw [hA1]; positivity
  have e1 : (2 * q * su * w1) ^ 2 = 4 * ψ * ((1 + ρ * x) * (1 - P1 + P1 * x)) := by
    linear_combination (4 * su ^ 2 * w1 ^ 2) * hqs + (4 * ψ * w1 ^ 2) * hsus +
      (4 * ψ * (1 + ρ * x)) * hw1s
  have hstep1 : 2 * q * su * w1 ≤ (1 - P1) * ρ + P1 + 2 * P1 * ρ * x := by
    apply sq_le_imp hA1p
    rw [e1]; exact h
  have hsq : (w1 - w2) * (w1 + w2) = (P2 - P1) * (1 - x) := by
    linear_combination hw1s - hw2s
  have hρx : 0 ≤ 1 - ρ * (1 - x) := by
    have := mul_le_mul_of_nonneg_left (by linarith : 1 - x ≤ 1) hρ0.le; linarith
  have key1 : (ρ * w1 * w2 - (1 + ρ * x) * P1) * (1 - x) ≤ (1 + ρ * x) * w1 * (w1 + w2) := by
    linarith [mul_nonneg (mul_pos hw1p hw2p).le hρx,
      mul_nonneg (mul_nonneg (by linarith : (0:ℝ) ≤ 1 + ρ * x) hP1.le) (by linarith : (0:ℝ) ≤ 1 - x),
      mul_nonneg (mul_pos hw1p (add_pos hw1p hw2p)).le (by positivity : (0:ℝ) ≤ ρ * x),
      mul_pos hw1p hw1p]
  have key2 : (ρ * w1 * w2 - (1 + ρ * x) * P1) * (w1 - w2) * (w1 + w2) ≤
      (1 + ρ * x) * (P2 - P1) * w1 * (w1 + w2) := by
    rw [mul_assoc (ρ * w1 * w2 - (1 + ρ * x) * P1), hsq]
    calc (ρ * w1 * w2 - (1 + ρ * x) * P1) * ((P2 - P1) * (1 - x))
        = (P2 - P1) * ((ρ * w1 * w2 - (1 + ρ * x) * P1) * (1 - x)) := by ring
      _ ≤ (P2 - P1) * ((1 + ρ * x) * w1 * (w1 + w2)) :=
          mul_le_mul_of_nonneg_left key1 (sub_nonneg.mpr h12)
      _ = (1 + ρ * x) * (P2 - P1) * w1 * (w1 + w2) := by ring
  have key3 : (ρ * w1 * w2 - (1 + ρ * x) * P1) * (w1 - w2) ≤ (1 + ρ * x) * (P2 - P1) * w1 :=
    le_of_mul_le_mul_right key2 (by linarith)
  have claim : ((1 - P1) * ρ + P1 + 2 * P1 * ρ * x) * w2 ≤
      ((1 - P2) * ρ + P2 + 2 * P2 * ρ * x) * w1 := by
    rw [hA1, hA2]; linarith [key3]
  have hstep2 : 2 * q * su * w2 ≤ (1 - P2) * ρ + P2 + 2 * P2 * ρ * x := by
    have : w1 * (2 * q * su * w2) ≤ w1 * ((1 - P2) * ρ + P2 + 2 * P2 * ρ * x) := by
      linarith [mul_le_mul_of_nonneg_right hstep1 hw2p.le, claim]
    exact le_of_mul_le_mul_left this hw1p
  have e2 : (2 * q * su * w2) * (2 * q * su * w2) = 4 * ψ * ((1 + ρ * x) * (1 - P2 + P2 * x)) := by
    linear_combination (4 * su ^ 2 * w2 ^ 2) * hqs + (4 * ψ * w2 ^ 2) * hsus +
      (4 * ψ * (1 + ρ * x)) * hw2s
  linarith [mul_self_le_mul_self (by positivity : (0:ℝ) ≤ 2 * q * su * w2) hstep2]

lemma mono_xi (ρ ψ P1 P2 : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hψ : 0 < ψ) (hP1 : 0 < P1)
    (h12 : P1 ≤ P2) (hP2 : P2 ≤ 1) : xiStar ρ ψ P1 ≤ xiStar ρ ψ P2 := by
  rcases xs_cases ρ ψ P2 with ⟨_, hx2⟩ | ⟨h2, hx2⟩
  · rw [hx2]; exact (xs_range ρ ψ P1).2
  · have h1 : P1 * ρ < ψ := by have := mul_le_mul_of_nonneg_right h12 hρ0.le; linarith
    rcases xs_cases ρ ψ P1 with ⟨h1', _⟩ | ⟨_, hx1⟩
    · exfalso; linarith
    · rw [hx1, hx2]
      rcases le_or_gt (min 1 (xiI ρ ψ P1)) 0 with h0 | h0
      · rw [max_eq_left h0]; exact le_max_left _ _
      · rw [max_eq_right h0.le]
        have hx1' : min 1 (xiI ρ ψ P1) ≤ 1 := min_le_left _ _
        have hxy : min 1 (xiI ρ ψ P1) ≤ xiI ρ ψ P1 := min_le_right _ _
        have hP1le : P1 ≤ 1 := le_trans h12 hP2
        have hc1 := ((xiI_le_iff ρ ψ P1 _ hρ0 hP1 hP1le h1 h0.le).1).1 hxy
        have hc2 := sc ρ ψ P1 P2 _ hρ0 hρ1 hψ hP1 h12 hP2 h0 hx1'
          (by linarith [conv_gen ρ ψ P1 (min 1 (xiI ρ ψ P1))])
        have hc3 := ((xiI_le_iff ρ ψ P2 _ hρ0 (by linarith) hP2 h2 h0.le).1).2
          (by linarith [conv_gen ρ ψ P2 (min 1 (xiI ρ ψ P1))])
        exact le_trans (le_min hx1' hc3) (le_max_right _ _)

lemma K_formula (ρ ψ P ξ r M : ℝ) (hρ0 : 0 < ρ) (hξ0 : 0 ≤ ξ) (hr : 0 < r) (hM0 : M ≠ 0)
    (hq : ρ * r ^ 2 - 2 * √ψ * r + P = 0) (hM : √ψ - ρ * r = M)
    (hxi : 2 * r * M * ξ = r ^ 2 - (1 - P)) :
    ξ * gv ρ ψ P ξ = Kf r P M := by
  have hv := v_eq ρ (√ψ) P r M ξ hq hM.symm hxi
  have hu : 0 ≤ 1 + ρ * ξ := by positivity
  have hs : √((1 + ρ * ξ) * (1 - P + P * ξ)) = r * (1 + ρ * ξ) := by
    rw [hv, show (1 + ρ * ξ) * (r ^ 2 * (1 + ρ * ξ)) = (r * (1 + ρ * ξ)) ^ 2 by ring]
    exact Real.sqrt_sq (by positivity)
  unfold gv Kf
  rw [hs, show r * (1 + ρ * ξ) - √ψ * ξ = r - M * ξ by rw [← hM]; ring]
  have hξ' : ξ = (r ^ 2 - (1 - P)) / (2 * r * M) := by
    rw [eq_div_iff (mul_ne_zero (mul_ne_zero two_ne_zero hr.ne') hM0)]
    linarith [hxi]
  rw [hξ']
  field_simp
  ring

lemma Kp_eq (ρ ψ P : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hD : P * ρ < ψ)
    (hd : 0 ≤ P - (1 - P) * ρ) (hξ : 0 ≤ xiI ρ ψ P) :
    xiI ρ ψ P * gv ρ ψ P (xiI ρ ψ P) = Kf (rp ρ ψ P) P (√(ψ - P * ρ)) := by
  obtain ⟨hr, hq, hM, hxi⟩ := branch_pos ρ ψ P hρ0 hP0 hD hd
  have hσ : 0 < √(ψ - P * ρ) := Real.sqrt_pos.mpr (by linarith)
  exact K_formula ρ ψ P _ _ _ hρ0 hξ hr hσ.ne' hq hM hxi

lemma Kn_eq (ρ ψ P : ℝ) (hρ0 : 0 < ρ) (hP0 : 0 < P) (hD : P * ρ < ψ)
    (hd : P - (1 - P) * ρ < 0) (hξ : 0 ≤ xiI ρ ψ P) :
    xiI ρ ψ P * gv ρ ψ P (xiI ρ ψ P) = Kf (rn ρ ψ P) P (-√(ψ - P * ρ)) := by
  obtain ⟨hr, hq, hM, hxi⟩ := branch_neg ρ ψ P hρ0 hP0 hD hd
  have hσ : 0 < √(ψ - P * ρ) := Real.sqrt_pos.mpr (by linarith)
  exact K_formula ρ ψ P _ _ _ hρ0 hξ hr (neg_ne_zero.mpr hσ.ne') hq hM hxi

lemma mono_pos_alg (r1 r2 s1 s2 a1 a2 : ℝ) (hr1 : 0 < r1) (hr12 : r1 ≤ r2) (hs2 : 0 < s2)
    (hs12 : s2 ≤ s1) (ha2 : 0 ≤ a2) (ha12 : a2 ≤ a1) (hN : a1 < r1 ^ 2) :
    (r1 ^ 2 - a1) * (r1 ^ 2 + a1) / (4 * r1 ^ 2 * s1) ≤
      (r2 ^ 2 - a2) * (r2 ^ 2 + a2) / (4 * r2 ^ 2 * s2) := by
  have hr2 : 0 < r2 := lt_of_lt_of_le hr1 hr12
  have hs1 : 0 < s1 := lt_of_lt_of_le hs2 hs12
  have e1 : (r1 ^ 2 - a1) * (r1 ^ 2 + a1) / (4 * r1 ^ 2 * s1) =
      (r1 ^ 2 - (a1 / r1) ^ 2) / (4 * s1) := by
    field_simp
    ring
  have e2 : (r2 ^ 2 - a2) * (r2 ^ 2 + a2) / (4 * r2 ^ 2 * s2) =
      (r2 ^ 2 - (a2 / r2) ^ 2) / (4 * s2) := by
    field_simp
    ring
  rw [e1, e2]
  have hy : a2 / r2 ≤ a1 / r1 := div_le_div₀ (by linarith) ha12 hr1 hr12
  have hy0 : 0 ≤ a2 / r2 := div_nonneg ha2 hr2.le
  have hy1 : a1 / r1 < r1 := by rw [div_lt_iff₀ hr1]; nlinarith
  have hy10 : 0 ≤ a1 / r1 := div_nonneg (by linarith) hr1.le
  have hX1 : 0 < r1 ^ 2 - (a1 / r1) ^ 2 := by nlinarith
  have hX : r1 ^ 2 - (a1 / r1) ^ 2 ≤ r2 ^ 2 - (a2 / r2) ^ 2 := by
    nlinarith [mul_le_mul hr12 hr12 hr1.le hr2.le, mul_le_mul hy hy hy0 hy10]
  exact div_le_div₀ (by linarith) hX (by positivity) (by linarith)

lemma mono_neg_alg (r1 r2 s1 s2 a1 a2 ρ q : ℝ) (hρ1 : ρ < 1) (hρ0 : 0 < ρ) (hr2 : 0 < r2)
    (hr21 : r2 ≤ r1) (hs2 : 0 < s2) (hs12 : s2 ≤ s1)
    (ha1 : a1 = 1 - 2 * q * r1 + ρ * r1 ^ 2) (ha2 : a2 = 1 - 2 * q * r2 + ρ * r2 ^ 2)
    (hN : r1 ^ 2 < a1) (ha1le : a1 ≤ 1) :
    (r1 ^ 2 - a1) * (r1 ^ 2 + a1) / (4 * r1 ^ 2 * (-s1)) ≤
      (r2 ^ 2 - a2) * (r2 ^ 2 + a2) / (4 * r2 ^ 2 * (-s2)) := by
  have hr1 : 0 < r1 := lt_of_lt_of_le hr2 hr21
  have hs1 : 0 < s1 := lt_of_lt_of_le hs2 hs12
  have e1 : (r1 ^ 2 - a1) * (r1 ^ 2 + a1) / (4 * r1 ^ 2 * (-s1)) =
      ((a1 / r1) ^ 2 - r1 ^ 2) / (4 * s1) := by
    field_simp
    ring
  have e2 : (r2 ^ 2 - a2) * (r2 ^ 2 + a2) / (4 * r2 ^ 2 * (-s2)) =
      ((a2 / r2) ^ 2 - r2 ^ 2) / (4 * s2) := by
    field_simp
    ring
  rw [e1, e2]
  have hrr : ρ * (r1 * r2) ≤ 1 := by
    have : r1 * r2 ≤ r1 ^ 2 := by nlinarith
    nlinarith [mul_pos hr1 hr2]
  have hy : a1 / r1 ≤ a2 / r2 := by
    rw [div_le_div_iff₀ hr1 hr2, ha1, ha2]
    nlinarith [mul_nonneg (sub_nonneg.mpr hr21) (sub_nonneg.mpr hrr)]
  have hy10 : 0 ≤ a1 / r1 := div_nonneg (by nlinarith) hr1.le
  have hy1 : r1 < a1 / r1 := by rw [lt_div_iff₀ hr1]; nlinarith
  have hX1 : 0 < (a1 / r1) ^ 2 - r1 ^ 2 := by nlinarith
  have hX : (a1 / r1) ^ 2 - r1 ^ 2 ≤ (a2 / r2) ^ 2 - r2 ^ 2 := by
    nlinarith [mul_le_mul hr21 hr21 hr2.le hr1.le, mul_le_mul hy hy hy10 (le_trans hy10 hy)]
  exact div_le_div₀ (by linarith) hX (by positivity) (by linarith)

lemma Kp_mono (ρ ψ P1 P2 : ℝ) (hρ0 : 0 < ρ) (hP1 : 0 < P1) (h12 : P1 ≤ P2) (hP2 : P2 ≤ 1)
    (hD2 : P2 * ρ < ψ) (hd1 : 0 ≤ P1 - (1 - P1) * ρ) (hξ1 : 0 < xiI ρ ψ P1) :
    Kf (rp ρ ψ P1) P1 (√(ψ - P1 * ρ)) ≤ Kf (rp ρ ψ P2) P2 (√(ψ - P2 * ρ)) := by
  have hD1 : P1 * ρ < ψ := by nlinarith
  obtain ⟨hr1, -, -, hxi1⟩ := branch_pos ρ ψ P1 hρ0 hP1 hD1 hd1
  have hs2 : 0 < √(ψ - P2 * ρ) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : 0 < √(ψ - P1 * ρ) := Real.sqrt_pos.mpr (by linarith)
  have hs12 : √(ψ - P2 * ρ) ≤ √(ψ - P1 * ρ) := Real.sqrt_le_sqrt (by nlinarith)
  have hr12 : rp ρ ψ P1 ≤ rp ρ ψ P2 := by
    unfold rp
    rw [div_le_div_iff₀ hρ0 hρ0]; nlinarith
  have hN : 1 - P1 < rp ρ ψ P1 ^ 2 := by
    have := mul_pos (mul_pos (mul_pos two_pos hr1) hs1) hξ1
    linarith
  unfold Kf
  exact mono_pos_alg _ _ _ _ _ _ hr1 hr12 hs2 hs12 (by linarith) (by linarith) hN

lemma Kn_mono (ρ ψ P1 P2 : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hP1 : 0 < P1) (h12 : P1 ≤ P2)
    (hP2 : P2 ≤ 1) (hD2 : P2 * ρ < ψ) (hd1 : P1 - (1 - P1) * ρ < 0)
    (hd2 : P2 - (1 - P2) * ρ < 0) (hξ1 : 0 < xiI ρ ψ P1) :
    Kf (rn ρ ψ P1) P1 (-√(ψ - P1 * ρ)) ≤ Kf (rn ρ ψ P2) P2 (-√(ψ - P2 * ρ)) := by
  have hD1 : P1 * ρ < ψ := by nlinarith
  obtain ⟨hr1, hq1, -, hxi1⟩ := branch_neg ρ ψ P1 hρ0 hP1 hD1 hd1
  obtain ⟨hr2, hq2, -, -⟩ := branch_neg ρ ψ P2 hρ0 (by linarith) hD2 hd2
  have hs2 : 0 < √(ψ - P2 * ρ) := Real.sqrt_pos.mpr (by linarith)
  have hs1 : 0 < √(ψ - P1 * ρ) := Real.sqrt_pos.mpr (by linarith)
  have hs12 : √(ψ - P2 * ρ) ≤ √(ψ - P1 * ρ) := Real.sqrt_le_sqrt (by nlinarith)
  have hr21 : rn ρ ψ P2 ≤ rn ρ ψ P1 := by
    unfold rn
    rw [div_le_div_iff₀ hρ0 hρ0]; nlinarith
  have hN : rn ρ ψ P1 ^ 2 < 1 - P1 := by
    have := mul_pos (mul_pos (mul_pos two_pos hr1) hs1) hξ1
    linarith
  unfold Kf
  exact mono_neg_alg _ _ _ _ _ _ ρ (√ψ) hρ1 hρ0 hr2 hr21 hs2 hs12 (by linarith) (by linarith)
    hN (by linarith)

lemma interior_extract (ρ ψ P : ℝ) (h0 : 0 < xiStar ρ ψ P) (h1 : xiStar ρ ψ P < 1) :
    P * ρ < ψ ∧ xiStar ρ ψ P = xiI ρ ψ P ∧ 0 < xiI ρ ψ P ∧ xiI ρ ψ P < 1 := by
  rcases xs_cases ρ ψ P with ⟨_, h⟩ | ⟨hD, hx⟩
  · rw [h] at h1; exact absurd h1 (lt_irrefl _)
  · rw [hx] at h0 h1 ⊢
    have hm : 0 < min 1 (xiI ρ ψ P) := by
      by_contra hc
      push_neg at hc
      rw [max_eq_left hc] at h0
      exact lt_irrefl _ h0
    rw [max_eq_right hm.le] at h0 h1 ⊢
    have hy : xiI ρ ψ P < 1 := by
      by_contra hc
      push_neg at hc
      rw [min_eq_left hc] at h1
      exact lt_irrefl _ h1
    rw [min_eq_right hy.le] at h0 ⊢
    exact ⟨hD, rfl, h0, hy⟩

lemma W_sq (ρ ψ : ℝ) (hρ0 : 0 < ρ) (hψ : 0 < ψ) :
    (2 * √ψ * √(1 + ρ)) ^ 2 = 4 * ψ * (1 + ρ) := by
  have h1 := Real.sq_sqrt hψ.le
  have h2 := Real.sq_sqrt (show (0 : ℝ) ≤ 1 + ρ by linarith)
  linear_combination (4 * √(1 + ρ) ^ 2) * h1 + (4 * ψ) * h2

lemma Phi_mono (ρ ψ P1 P2 : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hψ : 0 < ψ) (hP1 : 0 < P1)
    (h12 : P1 < P2) (hP2 : P2 ≤ 1) :
    xiStar ρ ψ P1 * gv ρ ψ P1 (xiStar ρ ψ P1) ≤ xiStar ρ ψ P2 * gv ρ ψ P2 (xiStar ρ ψ P2) := by
  have hP1le : P1 ≤ 1 := by linarith
  have hP2p : 0 < P2 := by linarith
  obtain ⟨hx10, hx11⟩ := xs_range ρ ψ P1
  obtain ⟨hx20, hx21⟩ := xs_range ρ ψ P2
  have hg2 := g_nonneg ρ ψ P2 hρ0 hψ hP2p hP2
  have hΦ2 : 0 ≤ xiStar ρ ψ P2 * gv ρ ψ P2 (xiStar ρ ψ P2) := mul_nonneg hx20 hg2
  have hmono := mono_xi ρ ψ P1 P2 hρ0 hρ1 hψ hP1 h12.le hP2
  rcases eq_or_lt_of_le hx10 with h0 | h0
  · rw [← h0, zero_mul]; exact hΦ2
  rcases eq_or_lt_of_le hx11 with h1 | h1
  · have h2 : xiStar ρ ψ P2 = 1 := le_antisymm hx21 (h1 ▸ hmono)
    rw [h1, h2, gv_one, gv_one]
  obtain ⟨hD1, hξ1e, hy1p, hy1l⟩ := interior_extract ρ ψ P1 h0 h1
  rw [hξ1e]
  have hW := W_sq ρ ψ hρ0 hψ
  have hlt1 : (ρ + P1 * (1 + ρ)) ^ 2 < 4 * ψ * (1 + ρ) := by
    have hk := (xiI_le_iff ρ ψ P1 1 hρ0 hP1 hP1le hD1 zero_le_one).1
    have h' : ¬ (4 * (ψ - P1 * ρ) * ((1 + ρ * 1) * (1 - P1 + P1 * 1)) ≤ (P1 - (1 - P1) * ρ) ^ 2) :=
      fun hh => absurd (hk.2 hh) (not_le.mpr hy1l)
    push_neg at h'
    linarith [conv1 ρ ψ P1]
  obtain ⟨P0, hP0d⟩ : ∃ P0 : ℝ, ρ + P0 * (1 + ρ) = 2 * √ψ * √(1 + ρ) :=
    ⟨(2 * √ψ * √(1 + ρ) - ρ) / (1 + ρ), by rw [div_mul_cancel₀ _ (by positivity)]; ring⟩
  have hP0sq : (ρ + P0 * (1 + ρ)) ^ 2 = 4 * ψ * (1 + ρ) := by rw [hP0d, hW]
  have hP10 : P1 < P0 := by
    have hpos : 0 ≤ ρ + P1 * (1 + ρ) := by positivity
    have : ρ + P1 * (1 + ρ) < ρ + P0 * (1 + ρ) := by
      by_contra hc
      push_neg at hc
      have h0' : 0 ≤ ρ + P0 * (1 + ρ) := by rw [hP0d]; positivity
      linarith [mul_self_le_mul_self h0' hc]
    by_contra hc
    push_neg at hc
    have := mul_le_mul_of_nonneg_right hc (by linarith : (0:ℝ) ≤ 1 + ρ)
    linarith
  have hD0of : P0 - (1 - P0) * ρ ≠ 0 → P0 * ρ < ψ := by
    intro hne
    have e : 4 * (1 + ρ) * (ψ - P0 * ρ) = (P0 - (1 - P0) * ρ) ^ 2 := by
      linear_combination (-1) * hP0sq
    have : 0 < (P0 - (1 - P0) * ρ) ^ 2 := by positivity
    by_contra hc
    push_neg at hc
    have : 4 * (1 + ρ) * (ψ - P0 * ρ) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
    linarith
  have hy0 : P0 * ρ < ψ → P0 ≤ 1 → xiI ρ ψ P0 = 1 := by
    intro hD0 hP01
    have hk := xiI_le_iff ρ ψ P0 1 hρ0 (by linarith) hP01 hD0 zero_le_one
    have e := conv1 ρ ψ P0
    apply le_antisymm
    · by_contra hc
      push_neg at hc
      have := hk.2.1 hc
      linarith
    · apply hk.1.2; linarith
  have hΦ2one : xiStar ρ ψ P2 = 1 →
      xiStar ρ ψ P2 * gv ρ ψ P2 (xiStar ρ ψ P2) = √(1 + ρ) - √ψ := by
    intro h; rw [h, one_mul, gv_one]
  have hP0P2 : xiStar ρ ψ P2 = 1 → P0 * ρ < ψ → P0 ≤ P2 := by
    intro h hD0
    rcases xs_cases ρ ψ P2 with ⟨h2, _⟩ | ⟨h2, hx2⟩
    · by_contra hc
      push_neg at hc
      have := mul_lt_mul_of_pos_right hc hρ0
      linarith
    · rw [hx2] at h
      have hy2 : 1 ≤ xiI ρ ψ P2 := by
        by_contra hc
        push_neg at hc
        rw [min_eq_right hc.le] at h
        have : max 0 (xiI ρ ψ P2) < 1 := max_lt one_pos hc
        linarith
      have := (xiI_le_iff ρ ψ P2 1 hρ0 hP2p hP2 h2 zero_le_one).1.1 hy2
      have h4 : 4 * ψ * (1 + ρ) ≤ (ρ + P2 * (1 + ρ)) ^ 2 := by linarith [conv1 ρ ψ P2]
      have h5 : ρ + P0 * (1 + ρ) ≤ ρ + P2 * (1 + ρ) :=
        sq_le_imp (by positivity) (by rw [hP0sq]; exact h4)
      exact le_of_mul_le_mul_right (by linarith) (by linarith : (0:ℝ) < 1 + ρ)
  rcases le_or_gt 0 (P1 - (1 - P1) * ρ) with hd1 | hd1
  · -- branch with d ≥ 0
    rw [Kp_eq ρ ψ P1 hρ0 hP1 hD1 hd1 hy1p.le]
    rcases eq_or_lt_of_le hx21 with h2 | h2
    · have hd0 : 0 < P0 - (1 - P0) * ρ := by
        have := mul_lt_mul_of_pos_right hP10 (by linarith : (0:ℝ) < 1 + ρ); linarith
      have hD0 := hD0of hd0.ne'
      have hP02 := hP0P2 h2 hD0
      have hP01 : P0 ≤ 1 := le_trans hP02 hP2
      have hy0e := hy0 hD0 hP01
      have hK0 := Kp_eq ρ ψ P0 hρ0 (by linarith) hD0 hd0.le (by rw [hy0e]; exact zero_le_one)
      rw [hy0e, one_mul, gv_one] at hK0
      rw [hΦ2one h2, hK0]
      exact Kp_mono ρ ψ P1 P0 hρ0 hP1 hP10.le hP01 hD0 hd1 hy1p
    · obtain ⟨hD2, hξ2e, hy2p, _⟩ := interior_extract ρ ψ P2 (lt_of_lt_of_le h0 hmono) h2
      have hd2 : 0 ≤ P2 - (1 - P2) * ρ := by
        have := mul_lt_mul_of_pos_right h12 (by linarith : (0:ℝ) < 1 + ρ); linarith
      rw [hξ2e, Kp_eq ρ ψ P2 hρ0 hP2p hD2 hd2 hy2p.le]
      exact Kp_mono ρ ψ P1 P2 hρ0 hP1 h12.le hP2 hD2 hd1 hy1p
  · -- branch with d < 0
    have hPm : ψ * (1 + ρ) < ρ ^ 2 := by
      rcases lt_trichotomy (ψ * (1 + ρ)) (ρ ^ 2) with h | h | h
      · exact h
      · exfalso
        have hk0 := (xiI_le_iff ρ ψ P1 0 hρ0 hP1 hP1le hD1 le_rfl).2.1 hy1p
        have e : (1 + ρ) ^ 2 * (4 * (ψ - P1 * ρ) * ((1 + ρ * 0) * (1 - P1 + P1 * 0)) -
            (P1 - (1 - P1) * ρ) ^ 2) =
            (ρ - P1 * (1 + ρ)) * (4 * ρ - (ρ - P1 * (1 + ρ)) * (1 - ρ) ^ 2) := by
          linear_combination (4 * (1 + ρ) * (1 - P1)) * h
        have he : 0 < ρ - P1 * (1 + ρ) := by linarith
        have hq1 : 0 ≤ 1 - (1 - ρ) ^ 2 := by nlinarith
        have he2 : 0 < 4 * ρ - (ρ - P1 * (1 + ρ)) * (1 - ρ) ^ 2 := by
          have := mul_nonneg he.le hq1
          have := mul_pos hP1 (by linarith : (0:ℝ) < 1 + ρ)
          linarith
        have h1r : 0 < (1 + ρ) ^ 2 := by positivity
        have hneg : (1 + ρ) ^ 2 * (4 * (ψ - P1 * ρ) * ((1 + ρ * 0) * (1 - P1 + P1 * 0)) -
            (P1 - (1 - P1) * ρ) ^ 2) < 0 := mul_neg_of_pos_of_neg h1r (by linarith)
        linarith [mul_pos he he2]
      · exfalso
        obtain ⟨Pm, hPmd⟩ : ∃ Pm : ℝ, Pm = ρ / (1 + ρ) := ⟨_, rfl⟩
        have h1ρ : (0:ℝ) < 1 + ρ := by linarith
        have hPm0 : 0 < Pm := by rw [hPmd]; exact div_pos hρ0 h1ρ
        have hPm1 : Pm < 1 := by rw [hPmd]; exact (div_lt_one h1ρ).mpr (by linarith)
        have hP1m : P1 < Pm := by rw [hPmd]; exact (lt_div_iff₀ h1ρ).mpr (by linarith)
        have hDm : Pm * ρ < ψ := by
          rw [hPmd, div_mul_eq_mul_div, div_lt_iff₀ h1ρ]; linarith
        have hdm : Pm - (1 - Pm) * ρ = 0 := by rw [hPmd]; field_simp; ring
        have hym : ¬ (0 < xiI ρ ψ Pm) := by
          intro hh
          have := (xiI_le_iff ρ ψ Pm 0 hρ0 hPm0 hPm1.le hDm le_rfl).2.1 hh
          rw [hdm] at this
          have : 0 < (ψ - Pm * ρ) * ((1 + ρ * 0) * (1 - Pm + Pm * 0)) := by
            apply mul_pos (by linarith)
            simp only [mul_zero, add_zero, one_mul]
            linarith
          linarith
        have hxm : xiStar ρ ψ Pm = 0 := by
          rcases xs_cases ρ ψ Pm with ⟨h', _⟩ | ⟨_, hx⟩
          · exfalso; linarith
          · rw [hx]
            push_neg at hym
            exact max_eq_left (le_trans (min_le_right _ _) hym)
        have := mono_xi ρ ψ P1 Pm hρ0 hρ1 hψ hP1 hP1m.le hPm1.le
        rw [hxm] at this
        linarith
    rw [Kn_eq ρ ψ P1 hρ0 hP1 hD1 hd1 hy1p.le]
    rcases eq_or_lt_of_le hx21 with h2 | h2
    · have hqw : √ψ * √(1 + ρ) < ρ := by
        by_contra hc
        push_neg at hc
        have := mul_self_le_mul_self hρ0.le hc
        linarith [hW]
      have hd0 : P0 - (1 - P0) * ρ < 0 := by linarith [hP0d]
      have hD0 := hD0of hd0.ne
      have hP01 : P0 ≤ 1 := by
        by_contra hc
        push_neg at hc
        have := mul_lt_mul_of_pos_right hc hρ0
        linarith
      have hy0e := hy0 hD0 hP01
      have hK0 := Kn_eq ρ ψ P0 hρ0 (by linarith) hD0 hd0 (by rw [hy0e]; exact zero_le_one)
      rw [hy0e, one_mul, gv_one] at hK0
      rw [hΦ2one h2, hK0]
      exact Kn_mono ρ ψ P1 P0 hρ0 hρ1 hP1 hP10.le hP01 hD0 hd1 hd0 hy1p
    · obtain ⟨hD2, hξ2e, hy2p, _⟩ := interior_extract ρ ψ P2 (lt_of_lt_of_le h0 hmono) h2
      have hd2 : P2 - (1 - P2) * ρ < 0 := by
        by_contra hc
        push_neg at hc
        linarith [mul_le_mul_of_nonneg_left hc hρ0.le,
          mul_lt_mul_of_pos_right hD2 (by linarith : (0:ℝ) < 1 + ρ)]
      rw [hξ2e, Kn_eq ρ ψ P2 hρ0 hP2p hD2 hd2 hy2p.le]
      exact Kn_mono ρ ψ P1 P2 hρ0 hρ1 hP1 h12.le hP2 hD2 hd1 hd2 hy1p

end DPHelp

open DigitalPrivacy.Strategy in
theorem solution (β ρ ψ : ℝ) (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 < ρ) (hρ1 : ρ < 1)
    (hψ : 0 < ψ) :
    (∀ P : ℝ, 0 < P → P ≤ 1 → IsBusinessOpt β ρ ψ P (xiStar ρ ψ P) (CStar β ρ ψ P)) ∧
    MonotoneOn (fun P => xiStar ρ ψ P) (Set.Ioc 0 1) ∧
    MonotoneOn (fun P => CStar β ρ ψ P) (Set.Ioc 0 1) := by
  refine ⟨fun P hP0 hP1 => (DPHelp.main1 β ρ ψ P hβ1 hρ0 hψ hP0 hP1).1, ?_, ?_⟩
  · intro a ha b hb hab
    exact DPHelp.mono_xi ρ ψ a b hρ0 hρ1 hψ ha.1 hab hb.2
  · intro a ha b hb hab
    rcases eq_or_lt_of_le hab with h | h
    · subst h; exact le_rfl
    · have hka := (DPHelp.main1 β ρ ψ a hβ1 hρ0 hψ ha.1 ha.2).2.2
      have hkb := (DPHelp.main1 β ρ ψ b hβ1 hρ0 hψ hb.1 hb.2).2.2
      have hΦ := DPHelp.Phi_mono ρ ψ a b hρ0 hρ1 hψ ha.1 h hb.2
      have hpos : 0 < (1 - β) * √ψ := mul_pos (by linarith) (Real.sqrt_pos.mpr hψ)
      have hc : CStar β ρ ψ a * ((1 - β) * √ψ) ≤ CStar β ρ ψ b * ((1 - β) * √ψ) := by
        rw [← mul_assoc, ← mul_assoc, hka, hkb]; exact hΦ
      exact le_of_mul_le_mul_right hc hpos
