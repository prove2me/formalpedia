-- Prove2me | solution 1 for DigitalPrivacy.DataStrategy.theorem_1_optimal_data_strategy
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-11-06T19:04:18.918839+00:00
-- url     : https://prove2.me/submissions/d3d9358c-a8e9-4a96-9a23-49be4295a1f0

import Mathlib
import Definitions.Def_DigitalPrivacy_Strategy_Setting
import Definitions.Def_DigitalPrivacy_DataStrategy_IsBusinessOptimal
import Definitions.Def_DigitalPrivacy_DataStrategy_cH
import Definitions.Def_DigitalPrivacy_DataStrategy_xiStar
import Definitions.Def_DigitalPrivacy_DataStrategy_cStar

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

namespace DPNew
open DigitalPrivacy.DataStrategy

lemma pos_of_prod {P ρ : ℝ} (hP0 : 0 ≤ P) (hρ0 : 0 ≤ ρ) (h : 0 < P * ρ) : 0 < P ∧ 0 < ρ :=
  ⟨lt_of_le_of_ne hP0 (fun e => by rw [← e, zero_mul] at h; exact lt_irrefl _ h),
    lt_of_le_of_ne hρ0 (fun e => by rw [← e, mul_zero] at h; exact lt_irrefl _ h)⟩

lemma xiI_bridge (ρ P ψ : ℝ) (h : 0 < P * ρ) :
    xiI ρ P ψ = DigitalPrivacy.Strategy.xiI ρ ψ P := by
  unfold xiI DigitalPrivacy.Strategy.xiI
  rw [if_pos h]

lemma xs_bridge (ρ P ψ : ℝ) (h : 0 < P * ρ) :
    xiStar ρ P ψ = DigitalPrivacy.Strategy.xiStar ρ ψ P := by
  unfold xiStar DigitalPrivacy.Strategy.xiStar
  rw [xiI_bridge ρ P ψ h]

lemma xs_cases_new (ρ P ψ : ℝ) : (ψ ≤ P * ρ ∧ xiStar ρ P ψ = 1) ∨
    (P * ρ < ψ ∧ xiStar ρ P ψ = max 0 (min 1 (xiI ρ P ψ))) := by
  unfold xiStar
  by_cases h : ψ ≤ P * ρ
  · left; exact ⟨h, if_pos h⟩
  · right; exact ⟨not_le.mp h, if_neg h⟩

lemma clamp_cases (X : ℝ) : (X ≤ 0 ∧ max 0 (min 1 X) = 0) ∨ (1 ≤ X ∧ max 0 (min 1 X) = 1) ∨
    (0 < X ∧ X < 1 ∧ max 0 (min 1 X) = X) := by
  rcases le_or_gt X 0 with h | h
  · left; exact ⟨h, max_eq_left (le_trans (min_le_right _ _) h)⟩
  · rcases le_or_gt 1 X with h1 | h1
    · right; left; exact ⟨h1, by rw [min_eq_left h1, max_eq_right zero_le_one]⟩
    · right; right; exact ⟨h, h1, by rw [min_eq_right h1.le, max_eq_right h.le]⟩

lemma clamp_le (X : ℝ) (h : 0 < max 0 (min 1 X)) : max 0 (min 1 X) ≤ X := by
  rcases clamp_cases X with ⟨_, hc⟩ | ⟨hX, hc⟩ | ⟨_, _, hc⟩
  · rw [hc] at h; exact absurd h (lt_irrefl 0)
  · rw [hc]; exact hX
  · rw [hc]

lemma xs_range_new (ρ P ψ : ℝ) : 0 ≤ xiStar ρ P ψ ∧ xiStar ρ P ψ ≤ 1 := by
  rcases xs_cases_new ρ P ψ with ⟨_, h⟩ | ⟨_, h⟩
  · rw [h]; exact ⟨zero_le_one, le_rfl⟩
  · rw [h]; exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩

lemma gv_corner (ρ ψ P y : ℝ) (h : P * ρ = 0) :
    DPHelp.gv ρ ψ P y = √(1 - P + (P + (1 - P) * ρ) * y) - √ψ * y := by
  unfold DPHelp.gv
  rw [show (1 + ρ * y) * (1 - P + P * y) = 1 - P + (P + (1 - P) * ρ) * y + (P * ρ) * y ^ 2 by ring,
    h, zero_mul, add_zero]

lemma tang (w s : ℝ) (hw : 0 ≤ w) (hs : 0 < s) : 2 * s * √w ≤ s ^ 2 + w := by
  linarith [sq_nonneg (√w - s), Real.sq_sqrt hw]

lemma xiI_corner_key (ρ P ψ : ℝ) (h : P * ρ = 0) (ha : 0 < P + (1 - P) * ρ) (hψ : 0 < ψ) :
    4 * (P + (1 - P) * ρ) * ψ * xiI ρ P ψ = (P + (1 - P) * ρ) ^ 2 - 4 * ψ * (1 - P) := by
  unfold xiI
  rw [if_neg (by rw [h]; exact lt_irrefl 0), if_pos ha]
  field_simp

lemma gmax_corner (ρ P ψ : ℝ) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ)
    (h0 : P * ρ = 0) :
    ∀ y, 0 ≤ y → y ≤ 1 → DPHelp.gv ρ ψ P y ≤ DPHelp.gv ρ ψ P (xiStar ρ P ψ) := by
  intro y hy0 hy1
  have hxs : xiStar ρ P ψ = max 0 (min 1 (xiI ρ P ψ)) := by
    unfold xiStar; rw [if_neg (by rw [h0]; exact not_le.mpr hψ)]
  have ha0 : 0 ≤ P + (1 - P) * ρ := add_nonneg hP0 (mul_nonneg (by linarith) hρ0)
  have hq0 : 0 < √ψ := Real.sqrt_pos.mpr hψ
  have hq2 : √ψ ^ 2 = ψ := Real.sq_sqrt hψ.le
  have hw : ∀ z, 0 ≤ z → 0 ≤ 1 - P + (P + (1 - P) * ρ) * z := fun z hz => by
    have := mul_nonneg ha0 hz; linarith
  have hb : ∀ s, 0 < s → ∀ z, 0 ≤ z → 2 * s * DPHelp.gv ρ ψ P z ≤
      s ^ 2 + (1 - P + (P + (1 - P) * ρ) * z) - 2 * s * √ψ * z := fun s hs z hz => by
    rw [gv_corner ρ ψ P z h0]
    have := tang _ _ (hw z hz) hs
    linarith
  rcases eq_or_lt_of_le ha0 with ha | ha
  · have hX : xiI ρ P ψ = 0 := by
      unfold xiI
      rw [if_neg (by rw [h0]; exact lt_irrefl 0), if_neg (by rw [← ha]; exact lt_irrefl 0)]
    rw [hxs, hX, min_eq_right zero_le_one, max_self, gv_corner ρ ψ P y h0, gv_corner ρ ψ P 0 h0,
      ← ha]
    have : 0 ≤ √ψ * y := mul_nonneg hq0.le hy0
    simp only [zero_mul, add_zero, mul_zero, sub_zero]
    linarith
  · have hkey := xiI_corner_key ρ P ψ h0 ha hψ
    have h4p : 0 < 4 * (P + (1 - P) * ρ) * ψ := mul_pos (mul_pos four_pos ha) hψ
    rw [hxs]
    rcases clamp_cases (xiI ρ P ψ) with ⟨hX, hc⟩ | ⟨hX, hc⟩ | ⟨hX0, hX1, hc⟩ <;> rw [hc]
    · have hl : 4 * (P + (1 - P) * ρ) * ψ * xiI ρ P ψ ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos h4p.le hX
      have hP1' : P < 1 := by
        by_contra hc'
        have hP : P = 1 := le_antisymm hP1 (not_lt.mp hc')
        rw [hP] at hl hkey
        linarith
      have hs0 : 0 < √(1 - P) := Real.sqrt_pos.mpr (by linarith)
      have hs2 : √(1 - P) ^ 2 = 1 - P := Real.sq_sqrt (by linarith)
      have e : (2 * √(1 - P) * √ψ) ^ 2 = 4 * ψ * (1 - P) := by
        rw [mul_pow, mul_pow, hs2, hq2]; ring
      have h4 : (P + (1 - P) * ρ) ^ 2 ≤ 4 * ψ * (1 - P) := by linarith
      have hA : P + (1 - P) * ρ ≤ 2 * √(1 - P) * √ψ :=
        DPHelp.sq_le_imp (by positivity) (by rw [e]; exact h4)
      have hb0 := hb _ hs0 y hy0
      rw [DPHelp.gv_zero]
      have : 2 * √(1 - P) * DPHelp.gv ρ ψ P y ≤ 2 * √(1 - P) * √(1 - P) := by
        linarith [mul_nonneg hy0 (sub_nonneg.mpr hA)]
      exact le_of_mul_le_mul_left this (by positivity)
    · have hs0 : 0 < √(1 + ρ) := Real.sqrt_pos.mpr (by linarith)
      have hs2 : √(1 + ρ) ^ 2 = 1 + ρ := Real.sq_sqrt (by linarith)
      have e : (2 * √(1 + ρ) * √ψ) ^ 2 = 4 * ψ * (1 + ρ) := by
        rw [mul_pow, mul_pow, hs2, hq2]; ring
      have h0' : ψ * (P * ρ) = 0 := by rw [h0, mul_zero]
      have h4 : 4 * ψ * (1 + ρ) ≤ (P + (1 - P) * ρ) ^ 2 := by
        linarith [mul_le_mul_of_nonneg_left hX h4p.le]
      have hA : 2 * √(1 + ρ) * √ψ ≤ P + (1 - P) * ρ :=
        DPHelp.sq_le_imp ha0 (by rw [e]; exact h4)
      have hb1 := hb _ hs0 y hy0
      rw [DPHelp.gv_one]
      have : 2 * √(1 + ρ) * DPHelp.gv ρ ψ P y ≤ 2 * √(1 + ρ) * (√(1 + ρ) - √ψ) := by
        have h0y : P * ρ * y = 0 := by rw [h0, zero_mul]
        linarith [mul_nonneg (sub_nonneg.mpr hA) (sub_nonneg.mpr hy1)]
      exact le_of_mul_le_mul_left this (by positivity)
    · have hs0 : 0 < (P + (1 - P) * ρ) / (2 * √ψ) := by positivity
      have hsq : 2 * ((P + (1 - P) * ρ) / (2 * √ψ)) * √ψ = P + (1 - P) * ρ := by
        field_simp
      have e1 : 4 * ψ * ((P + (1 - P) * ρ) / (2 * √ψ)) ^ 2 = (P + (1 - P) * ρ) ^ 2 := by
        rw [div_pow, mul_pow, hq2]; field_simp; ring
      have h4 : 4 * ψ * (1 - P + (P + (1 - P) * ρ) * xiI ρ P ψ) =
          4 * ψ * ((P + (1 - P) * ρ) / (2 * √ψ)) ^ 2 := by
        rw [e1]; linear_combination hkey
      have hwX : 1 - P + (P + (1 - P) * ρ) * xiI ρ P ψ = ((P + (1 - P) * ρ) / (2 * √ψ)) ^ 2 :=
        mul_left_cancel₀ (by positivity) h4
      have hgX : DPHelp.gv ρ ψ P (xiI ρ P ψ) =
          (P + (1 - P) * ρ) / (2 * √ψ) - √ψ * xiI ρ P ψ := by
        rw [gv_corner ρ ψ P _ h0, hwX, Real.sqrt_sq hs0.le]
      have hby := hb _ hs0 y hy0
      have hay : (P + (1 - P) * ρ) * y = 2 * ((P + (1 - P) * ρ) / (2 * √ψ)) * √ψ * y := by
        rw [hsq]
      have hax : (P + (1 - P) * ρ) * xiI ρ P ψ =
          2 * ((P + (1 - P) * ρ) / (2 * √ψ)) * √ψ * xiI ρ P ψ := by rw [hsq]
      have : 2 * ((P + (1 - P) * ρ) / (2 * √ψ)) * DPHelp.gv ρ ψ P y ≤
          2 * ((P + (1 - P) * ρ) / (2 * √ψ)) * DPHelp.gv ρ ψ P (xiI ρ P ψ) := by
        rw [hgX]; linarith
      exact le_of_mul_le_mul_left this (by positivity)

lemma gmax_new (ρ P ψ : ℝ) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ) :
    ∀ y, 0 ≤ y → y ≤ 1 → DPHelp.gv ρ ψ P y ≤ DPHelp.gv ρ ψ P (xiStar ρ P ψ) := by
  by_cases hPρ : 0 < P * ρ
  · obtain ⟨hP, hρ⟩ := pos_of_prod hP0 hρ0 hPρ
    rw [xs_bridge ρ P ψ hPρ]
    exact DPHelp.gmax ρ ψ P hρ hψ hP hP1
  · exact gmax_corner ρ P ψ hρ0 hP0 hP1 hψ
      (le_antisymm (not_lt.mp hPρ) (mul_nonneg hP0 hρ0))

lemma gv_pos_some (ρ P ψ : ℝ) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ) :
    ∃ y, 0 ≤ y ∧ y ≤ 1 ∧ 0 < DPHelp.gv ρ ψ P y := by
  obtain ⟨q, hq⟩ : ∃ q, q = √ψ := ⟨_, rfl⟩
  have hq0 : 0 ≤ q := by rw [hq]; exact Real.sqrt_nonneg _
  obtain ⟨s, hsd⟩ : ∃ s, s = 1 / (2 * (1 + q)) := ⟨_, rfl⟩
  have hs0 : 0 < s := by rw [hsd]; positivity
  have hs : 2 * (1 + q) * s = 1 := by rw [hsd]; field_simp
  have hs1 : s ≤ 1 / 2 := by linarith [mul_nonneg hq0 hs0.le]
  refine ⟨s ^ 2, by positivity, by nlinarith, ?_⟩
  unfold DPHelp.gv
  rw [← hq]
  have hv : 0 ≤ 1 - P + P * s ^ 2 := by linarith [mul_nonneg hP0 (sq_nonneg s)]
  have hU : s ^ 2 ≤ (1 + ρ * s ^ 2) * (1 - P + P * s ^ 2) := by
    linarith [mul_nonneg (mul_nonneg hρ0 (sq_nonneg s)) hv,
      mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P) (by nlinarith : (0:ℝ) ≤ 1 - s ^ 2)]
  have hS : s ≤ √((1 + ρ * s ^ 2) * (1 - P + P * s ^ 2)) := by
    have := Real.sqrt_le_sqrt hU
    rwa [Real.sqrt_sq hs0.le] at this
  have hqs : q * s ^ 2 = s * (1 - 2 * s) / 2 := by linear_combination (s / 2) * hs
  linarith [sq_nonneg s]

lemma gpos (ρ P ψ : ℝ) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ) :
    0 < DPHelp.gv ρ ψ P (xiStar ρ P ψ) := by
  obtain ⟨y, hy0, hy1, hy⟩ := gv_pos_some ρ P ψ hρ0 hP0 hP1 hψ
  exact lt_of_lt_of_le hy (gmax_new ρ P ψ hρ0 hP0 hP1 hψ y hy0 hy1)

/-! profit algebra -/

lemma profit0 (β ρ P ψ C : ℝ) : profit β ρ P ψ 0 C = (1 - P) * (1 / (1 - β)) - ψ * C := by
  unfold profit abarStar
  rw [if_pos rfl]
  ring

lemma profit_pos' (β ρ P ψ ξ C : ℝ) (hξ : ξ ≠ 0) (ht : C * (1 - β) + ξ ^ 2 ≠ 0) :
    (1 - β) * profit β ρ P ψ ξ C =
      C * (1 - β) * ((1 + ρ * ξ) * (1 - P + P * ξ) / (C * (1 - β) + ξ ^ 2) - ψ) := by
  unfold profit abarStar
  rw [if_neg hξ]
  field_simp

lemma alg_main (S q ξ t U ψ c : ℝ) (ht : 0 < t) (hS2 : S ^ 2 = U) (hq2 : q ^ 2 = ψ)
    (hc : c = t - ξ ^ 2) :
    c * (U / t - ψ) = (S - q * ξ) ^ 2 - (q * t - ξ * S) ^ 2 / t := by
  subst hS2 hq2 hc
  field_simp
  ring

lemma cH_formula (β ρ P ψ ξ : ℝ) (hψ : 0 < ψ) (hβ1 : β < 1) :
    cH β ρ P ψ ξ = ξ * DPHelp.gv ρ ψ P ξ / (√ψ * (1 - β)) := by
  have hq0 : 0 < √ψ := Real.sqrt_pos.mpr hψ
  have hβ' : (1 - β) ≠ 0 := by linarith
  unfold cH DPHelp.gv
  rw [show (1 / ψ) * (1 + ρ * ξ) * (1 - P + P * ξ) = ((1 + ρ * ξ) * (1 - P + P * ξ)) / ψ by ring,
    Real.sqrt_div' _ hψ.le]
  field_simp
  ring

lemma cStar_eq (β ρ P ψ : ℝ) : cStar β ρ P ψ = cH β ρ P ψ (xiStar ρ P ψ) := by
  unfold cStar cH
  rw [show 1 - P * (1 - xiStar ρ P ψ) = 1 - P + P * xiStar ρ P ψ by ring]
  ring

lemma val_bound (β ρ P ψ ξ C m : ℝ) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (hψ : 0 < ψ) (hξ0 : 0 ≤ ξ) (hξ1 : ξ ≤ 1) (hC : 0 ≤ C) (hm : 0 < m)
    (hg : DPHelp.gv ρ ψ P ξ ≤ m) (hg0 : DPHelp.gv ρ ψ P 0 ≤ m) :
    (1 - β) * profit β ρ P ψ ξ C ≤ m ^ 2 ∧
      ((1 - β) * profit β ρ P ψ ξ C = m ^ 2 → DPHelp.gv ρ ψ P ξ = m ∧ C = cH β ρ P ψ ξ) := by
  have hβ' : 0 < 1 - β := by linarith
  have e1 : (1 - β) * (1 / (1 - β)) = 1 := mul_one_div_cancel hβ'.ne'
  rcases eq_or_lt_of_le hξ0 with h0 | hpos
  · subst h0
    rw [profit0]
    have hz := DPHelp.gv_zero ρ ψ P
    have hs0 : 0 ≤ √(1 - P) := Real.sqrt_nonneg _
    have hs2 : √(1 - P) ^ 2 = 1 - P := Real.sq_sqrt (by linarith)
    rw [hz] at hg0
    have e : (1 - β) * ((1 - P) * (1 / (1 - β)) - ψ * C) = (1 - P) - (1 - β) * ψ * C := by
      linear_combination (1 - P) * e1
    rw [e]
    have hψC : 0 ≤ (1 - β) * ψ * C := mul_nonneg (mul_nonneg hβ'.le hψ.le) hC
    have hm2 : (1 - P) ≤ m ^ 2 := by rw [← hs2]; exact pow_le_pow_left₀ hs0 hg0 2
    refine ⟨by linarith, fun heq => ?_⟩
    have hC0 : C = 0 := by
      have h' : (1 - β) * ψ * C = 0 := by linarith
      rcases mul_eq_zero.mp h' with h | h
      · exfalso; have := mul_pos hβ' hψ; linarith
      · exact h
    refine ⟨?_, ?_⟩
    · rw [hz]
      have h1 : 1 - P = m ^ 2 := by rw [hC0] at heq; linarith
      exact le_antisymm hg0 (DPHelp.sq_le_imp hs0 (by rw [hs2]; linarith))
    · rw [hC0]; unfold cH; simp
  · have ht : 0 < C * (1 - β) + ξ ^ 2 :=
      add_pos_of_nonneg_of_pos (mul_nonneg hC hβ'.le) (by positivity)
    have hU : 0 ≤ (1 + ρ * ξ) * (1 - P + P * ξ) :=
      mul_nonneg (by positivity) (by linarith [mul_nonneg hP0 hξ0])
    obtain ⟨S, hS⟩ : ∃ S, S = √((1 + ρ * ξ) * (1 - P + P * ξ)) := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = √ψ := ⟨_, rfl⟩
    have hS0 : 0 ≤ S := by rw [hS]; exact Real.sqrt_nonneg _
    have hS2 : S ^ 2 = (1 + ρ * ξ) * (1 - P + P * ξ) := by rw [hS]; exact Real.sq_sqrt hU
    have hq0 : 0 < q := by rw [hq]; exact Real.sqrt_pos.mpr hψ
    have hq2 : q ^ 2 = ψ := by rw [hq]; exact Real.sq_sqrt hψ.le
    have hgv : DPHelp.gv ρ ψ P ξ = S - q * ξ := by unfold DPHelp.gv; rw [hS, hq]
    have hp := profit_pos' β ρ P ψ ξ C hpos.ne' ht.ne'
    have hid : (1 - β) * profit β ρ P ψ ξ C =
        (S - q * ξ) ^ 2 - (q * (C * (1 - β) + ξ ^ 2) - ξ * S) ^ 2 / (C * (1 - β) + ξ ^ 2) := by
      rw [hp]; exact alg_main S q ξ _ _ ψ _ ht hS2 hq2 (by ring)
    have hX : 0 ≤ (q * (C * (1 - β) + ξ ^ 2) - ξ * S) ^ 2 / (C * (1 - β) + ξ ^ 2) :=
      div_nonneg (sq_nonneg _) ht.le
    rw [hgv] at hg
    have hneg : S - q * ξ < 0 → (1 - β) * profit β ρ P ψ ξ C ≤ 0 := by
      intro hlt
      rw [hp]
      apply mul_nonpos_of_nonneg_of_nonpos (mul_nonneg hC hβ'.le)
      rw [sub_nonpos, div_le_iff₀ ht]
      have h1 : S ^ 2 ≤ (q * ξ) ^ 2 := pow_le_pow_left₀ hS0 (by linarith) 2
      rw [mul_pow, hq2] at h1
      linarith [mul_nonneg (mul_nonneg hψ.le hC) hβ'.le]
    have hm2 : 0 < m ^ 2 := pow_pos hm 2
    refine ⟨?_, ?_⟩
    · by_cases hgs : 0 ≤ S - q * ξ
      · have : (S - q * ξ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hgs hg 2
        linarith
      · have := hneg (lt_of_not_ge hgs); linarith
    · intro heq
      have hgs : 0 ≤ S - q * ξ := by
        by_contra hc; have := hneg (lt_of_not_ge hc); linarith
      have h1 : (S - q * ξ) ^ 2 ≤ m ^ 2 := pow_le_pow_left₀ hgs hg 2
      have h2 : m ^ 2 ≤ (S - q * ξ) ^ 2 := by linarith
      have hX0 : (q * (C * (1 - β) + ξ ^ 2) - ξ * S) ^ 2 / (C * (1 - β) + ξ ^ 2) = 0 := by
        linarith
      have hgm : S - q * ξ = m := le_antisymm hg (DPHelp.sq_le_imp hgs h2)
      have hsq : q * (C * (1 - β) + ξ ^ 2) - ξ * S = 0 := by
        rcases div_eq_zero_iff.mp hX0 with h | h
        · exact pow_eq_zero_iff two_ne_zero |>.mp h
        · exfalso; exact ht.ne' h
      refine ⟨by rw [hgv]; exact hgm, ?_⟩
      rw [cH_formula β ρ P ψ ξ hψ hβ1, hgv, ← hq, eq_div_iff (mul_pos hq0 hβ').ne']
      linear_combination hsq

lemma attain (β ρ P ψ ξ m : ℝ) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (hψ : 0 < ψ) (hξ0 : 0 ≤ ξ) (hm0 : 0 < m) (hgm : DPHelp.gv ρ ψ P ξ = m) :
    (1 - β) * profit β ρ P ψ ξ (cH β ρ P ψ ξ) = m ^ 2 ∧ 0 ≤ cH β ρ P ψ ξ := by
  have hβ' : 0 < 1 - β := by linarith
  have hq0 : 0 < √ψ := Real.sqrt_pos.mpr hψ
  have hcH := cH_formula β ρ P ψ ξ hψ hβ1
  have hcn : 0 ≤ cH β ρ P ψ ξ := by
    rw [hcH, hgm]; exact div_nonneg (mul_nonneg hξ0 hm0.le) (mul_pos hq0 hβ').le
  refine ⟨?_, hcn⟩
  rcases eq_or_lt_of_le hξ0 with h0 | hpos
  · subst h0
    have e1 : (1 - β) * (1 / (1 - β)) = 1 := mul_one_div_cancel hβ'.ne'
    have hc0 : cH β ρ P ψ 0 = 0 := by unfold cH; simp
    rw [hc0, profit0]
    rw [DPHelp.gv_zero] at hgm
    rw [← hgm, Real.sq_sqrt (by linarith)]
    linear_combination (1 - P) * e1
  · have hC1 : cH β ρ P ψ ξ * (1 - β) = ξ * m / √ψ := by
      rw [hcH, hgm]; field_simp
    have ht : 0 < cH β ρ P ψ ξ * (1 - β) + ξ ^ 2 :=
      add_pos_of_nonneg_of_pos (mul_nonneg hcn hβ'.le) (by positivity)
    have hU : 0 ≤ (1 + ρ * ξ) * (1 - P + P * ξ) :=
      mul_nonneg (by positivity) (by linarith [mul_nonneg hP0 hξ0])
    obtain ⟨S, hS⟩ : ∃ S, S = √((1 + ρ * ξ) * (1 - P + P * ξ)) := ⟨_, rfl⟩
    obtain ⟨q, hq⟩ : ∃ q, q = √ψ := ⟨_, rfl⟩
    have hS2 : S ^ 2 = (1 + ρ * ξ) * (1 - P + P * ξ) := by rw [hS]; exact Real.sq_sqrt hU
    have hq2 : q ^ 2 = ψ := by rw [hq]; exact Real.sq_sqrt hψ.le
    have hqp : 0 < q := by rw [hq]; exact hq0
    have hgv : DPHelp.gv ρ ψ P ξ = S - q * ξ := by unfold DPHelp.gv; rw [hS, hq]
    have hp := profit_pos' β ρ P ψ ξ (cH β ρ P ψ ξ) hpos.ne' ht.ne'
    rw [hp, alg_main S q ξ _ _ ψ _ ht hS2 hq2 (by ring)]
    have hqm : q * (ξ * m / q) = ξ * m := by field_simp
    have hz : q * (cH β ρ P ψ ξ * (1 - β) + ξ ^ 2) - ξ * S = 0 := by
      rw [hC1, ← hq, mul_add, hqm]
      rw [hgv] at hgm
      linear_combination (-ξ) * hgm
    rw [hz]
    rw [hgv] at hgm
    rw [hgm]
    ring

lemma opt_iff (β ρ P ψ xs : ℝ) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1)
    (hψ : 0 < ψ) (hxs : xs ∈ Set.Icc (0 : ℝ) 1)
    (hmax : ∀ y ∈ Set.Icc (0 : ℝ) 1, DPHelp.gv ρ ψ P y ≤ DPHelp.gv ρ ψ P xs)
    (hpos : 0 < DPHelp.gv ρ ψ P xs) (ξ C : ℝ) :
    IsBusinessOptimal β ρ P ψ ξ C ↔
      (ξ ∈ Set.Icc (0 : ℝ) 1 ∧ ∀ y ∈ Set.Icc (0 : ℝ) 1, DPHelp.gv ρ ψ P y ≤ DPHelp.gv ρ ψ P ξ) ∧
        C = cH β ρ P ψ ξ := by
  have hβ' : 0 < 1 - β := by linarith
  have hatt := attain β ρ P ψ xs _ hβ1 hρ0 hP0 hP1 hψ hxs.1 hpos rfl
  have hg0 : DPHelp.gv ρ ψ P 0 ≤ DPHelp.gv ρ ψ P xs := hmax 0 ⟨le_rfl, zero_le_one⟩
  constructor
  · rintro ⟨hξ, hC, hall⟩
    have h1 := hall xs (cH β ρ P ψ xs) hxs hatt.2
    have hb := val_bound β ρ P ψ ξ C _ hβ1 hρ0 hP0 hP1 hψ hξ.1 hξ.2 hC hpos (hmax ξ hξ) hg0
    have heq : (1 - β) * profit β ρ P ψ ξ C = DPHelp.gv ρ ψ P xs ^ 2 :=
      le_antisymm hb.1 (by rw [← hatt.1]; exact mul_le_mul_of_nonneg_left h1 hβ'.le)
    obtain ⟨hgm, hCe⟩ := hb.2 heq
    exact ⟨⟨hξ, fun y hy => by rw [hgm]; exact hmax y hy⟩, hCe⟩
  · rintro ⟨⟨hξ, hξmax⟩, rfl⟩
    have hgm : DPHelp.gv ρ ψ P ξ = DPHelp.gv ρ ψ P xs := le_antisymm (hmax ξ hξ) (hξmax xs hxs)
    have hatt' := attain β ρ P ψ ξ _ hβ1 hρ0 hP0 hP1 hψ hξ.1 hpos hgm
    refine ⟨hξ, hatt'.2, fun ξ' C' hξ' hC' => ?_⟩
    have hb := (val_bound β ρ P ψ ξ' C' _ hβ1 hρ0 hP0 hP1 hψ hξ'.1 hξ'.2 hC' hpos
      (hmax ξ' hξ') hg0).1
    have : (1 - β) * profit β ρ P ψ ξ' C' ≤ (1 - β) * profit β ρ P ψ ξ (cH β ρ P ψ ξ) := by
      rw [hatt'.1]; exact hb
    exact le_of_mul_le_mul_left this hβ'

/-! uniqueness and the knife-edge -/

lemma sqrt_mid (a b c d : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) (hd : 0 ≤ d)
    (hne : a * d ≠ b * c) : √(a * b) + √(c * d) < √((a + c) * (b + d)) := by
  rw [Real.sqrt_mul ha, Real.sqrt_mul hc]
  have hA := Real.sq_sqrt ha
  have hB := Real.sq_sqrt hb
  have hC := Real.sq_sqrt hc
  have hD := Real.sq_sqrt hd
  have hne' : √a * √d ≠ √b * √c := by
    intro h
    apply hne
    have h2 : (√a * √d) ^ 2 = (√b * √c) ^ 2 := by rw [h]
    rw [mul_pow, mul_pow, hA, hB, hC, hD] at h2
    exact h2
  rw [Real.lt_sqrt (by positivity)]
  have key : (a + c) * (b + d) - (√a * √b + √c * √d) ^ 2 = (√a * √d - √b * √c) ^ 2 := by
    rw [show (a + c) * (b + d) = (√a ^ 2 + √c ^ 2) * (√b ^ 2 + √d ^ 2) by rw [hA, hB, hC, hD]]
    ring
  have hpos : 0 < (√a * √d - √b * √c) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 (sub_ne_zero.mpr hne')))
  linarith

lemma gv_mid (ρ ψ P ξ1 ξ2 : ℝ) (hu1 : 0 ≤ 1 + ρ * ξ1) (hu2 : 0 ≤ 1 + ρ * ξ2)
    (hv1 : 0 ≤ 1 - P + P * ξ1) (hv2 : 0 ≤ 1 - P + P * ξ2) :
    2 * DPHelp.gv ρ ψ P ((ξ1 + ξ2) / 2) - DPHelp.gv ρ ψ P ξ1 - DPHelp.gv ρ ψ P ξ2 =
      √(((1 + ρ * ξ1) + (1 + ρ * ξ2)) * ((1 - P + P * ξ1) + (1 - P + P * ξ2))) -
        √((1 + ρ * ξ1) * (1 - P + P * ξ1)) - √((1 + ρ * ξ2) * (1 - P + P * ξ2)) := by
  unfold DPHelp.gv
  rw [show (1 + ρ * ((ξ1 + ξ2) / 2)) * (1 - P + P * ((ξ1 + ξ2) / 2)) =
      (((1 + ρ * ξ1) + (1 + ρ * ξ2)) * ((1 - P + P * ξ1) + (1 - P + P * ξ2))) / 2 ^ 2 by ring,
    Real.sqrt_div' _ (by positivity), Real.sqrt_sq (by norm_num : (0:ℝ) ≤ 2)]
  ring

lemma gv_affine (ρ ψ P y : ℝ) (hP1 : P ≤ 1) (hρ0 : 0 ≤ ρ) (hy : 0 ≤ y) (hk : P * (1 + ρ) = ρ) :
    DPHelp.gv ρ ψ P y = √(1 - P) * (1 + ρ * y) - √ψ * y := by
  unfold DPHelp.gv
  rw [show (1 + ρ * y) * (1 - P + P * y) = (1 - P) * (1 + ρ * y) ^ 2 by
      linear_combination (1 + ρ * y) * y * hk,
    Real.sqrt_mul (by linarith), Real.sqrt_sq (by positivity)]

lemma knife (ρ ψ P y : ℝ) (hP1 : P ≤ 1) (hρ0 : 0 ≤ ρ) (hy : 0 ≤ y) (hk : P * (1 + ρ) = ρ)
    (hψe : ψ = P * ρ) : DPHelp.gv ρ ψ P y = √(1 - P) := by
  rw [gv_affine ρ ψ P y hP1 hρ0 hy hk]
  have : √ψ = √(1 - P) * ρ := by
    rw [hψe, show P * ρ = (1 - P) * ρ ^ 2 by linear_combination ρ * hk,
      Real.sqrt_mul (by linarith), Real.sqrt_sq hρ0]
  rw [this]
  ring

lemma uniq (ρ ψ P ξ1 ξ2 : ℝ) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ)
    (hnk : ¬ (P * (1 + ρ) = ρ ∧ ψ = P * ρ)) (h1 : ξ1 ∈ Set.Icc (0 : ℝ) 1)
    (h2 : ξ2 ∈ Set.Icc (0 : ℝ) 1)
    (hm1 : ∀ y ∈ Set.Icc (0 : ℝ) 1, DPHelp.gv ρ ψ P y ≤ DPHelp.gv ρ ψ P ξ1)
    (hm2 : ∀ y ∈ Set.Icc (0 : ℝ) 1, DPHelp.gv ρ ψ P y ≤ DPHelp.gv ρ ψ P ξ2) : ξ1 = ξ2 := by
  have he : DPHelp.gv ρ ψ P ξ1 = DPHelp.gv ρ ψ P ξ2 := le_antisymm (hm2 ξ1 h1) (hm1 ξ2 h2)
  by_contra hne
  by_cases hk : P * (1 + ρ) = ρ
  · have hψne : ψ ≠ P * ρ := fun h => hnk ⟨hk, h⟩
    rw [gv_affine ρ ψ P ξ1 hP1 hρ0 h1.1 hk, gv_affine ρ ψ P ξ2 hP1 hρ0 h2.1 hk] at he
    have hz : (√(1 - P) * ρ - √ψ) * (ξ1 - ξ2) = 0 := by linear_combination he
    rcases mul_eq_zero.mp hz with h | h
    · apply hψne
      have hq : √ψ = √(1 - P) * ρ := by linarith
      have hsq : √ψ ^ 2 = (√(1 - P) * ρ) ^ 2 := by rw [hq]
      rw [mul_pow, Real.sq_sqrt hψ.le, Real.sq_sqrt (by linarith)] at hsq
      linear_combination hsq - ρ * hk
    · exact hne (by linarith)
  · have hmI : (ξ1 + ξ2) / 2 ∈ Set.Icc (0 : ℝ) 1 :=
      ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2]⟩
    have hgm := hm1 _ hmI
    have hu1 : 0 ≤ 1 + ρ * ξ1 := by have := mul_nonneg hρ0 h1.1; linarith
    have hu2 : 0 ≤ 1 + ρ * ξ2 := by have := mul_nonneg hρ0 h2.1; linarith
    have hv1 : 0 ≤ 1 - P + P * ξ1 := by have := mul_nonneg hP0 h1.1; linarith
    have hv2 : 0 ≤ 1 - P + P * ξ2 := by have := mul_nonneg hP0 h2.1; linarith
    have hmid := gv_mid ρ ψ P ξ1 ξ2 hu1 hu2 hv1 hv2
    have hne' : (1 + ρ * ξ1) * (1 - P + P * ξ2) ≠ (1 - P + P * ξ1) * (1 + ρ * ξ2) := by
      intro h
      have e : (1 + ρ * ξ1) * (1 - P + P * ξ2) - (1 - P + P * ξ1) * (1 + ρ * ξ2) =
          (ξ2 - ξ1) * (P * (1 + ρ) - ρ) := by ring
      rw [h, sub_self] at e
      rcases mul_eq_zero.mp e.symm with h' | h'
      · exact hne (by linarith)
      · exact hk (by linarith)
    have hlt := sqrt_mid _ _ _ _ hu1 hv1 hu2 hv2 hne'
    linarith

/-! monotonicity of ξ* -/

lemma Dmono (ρ ψ P1 P2 x : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hψ : 0 ≤ ψ) (hP1 : 0 ≤ P1)
    (h12 : P1 ≤ P2) (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (h : 4 * ψ * ((1 + ρ * x) * (1 - P1 + P1 * x)) ≤ ((1 - P1) * ρ + P1 + 2 * P1 * ρ * x) ^ 2) :
    4 * ψ * ((1 + ρ * x) * (1 - P2 + P2 * x)) ≤ ((1 - P2) * ρ + P2 + 2 * P2 * ρ * x) ^ 2 := by
  have hc : 0 ≤ 1 - ρ + 2 * ρ * x := by linarith [mul_nonneg hρ0 hx0]
  have key : (((1 - P2) * ρ + P2 + 2 * P2 * ρ * x) ^ 2 - 4 * ψ * ((1 + ρ * x) * (1 - P2 + P2 * x))) -
      (((1 - P1) * ρ + P1 + 2 * P1 * ρ * x) ^ 2 - 4 * ψ * ((1 + ρ * x) * (1 - P1 + P1 * x))) =
      (P2 - P1) * ((1 - ρ + 2 * ρ * x) * (2 * ρ + (P1 + P2) * (1 - ρ + 2 * ρ * x)) +
        4 * ψ * (1 + ρ * x) * (1 - x)) := by ring
  have hb : 0 ≤ (P2 - P1) * ((1 - ρ + 2 * ρ * x) * (2 * ρ + (P1 + P2) * (1 - ρ + 2 * ρ * x)) +
        4 * ψ * (1 + ρ * x) * (1 - x)) := by
    apply mul_nonneg (by linarith)
    apply add_nonneg
    · exact mul_nonneg hc (add_nonneg (by linarith) (mul_nonneg (by linarith) hc))
    · exact mul_nonneg (mul_nonneg (by linarith) (by linarith [mul_nonneg hρ0 hx0]))
        (by linarith)
  linarith

lemma B_gen (ρ P ψ : ℝ) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ)
    (hx : 0 < xiStar ρ P ψ) :
    4 * ψ * ((1 + ρ * xiStar ρ P ψ) * (1 - P + P * xiStar ρ P ψ)) ≤
      ((1 - P) * ρ + P + 2 * P * ρ * xiStar ρ P ψ) ^ 2 := by
  rcases xs_cases_new ρ P ψ with ⟨h, hx1⟩ | ⟨h, hx1⟩
  · rw [hx1]
    linarith [sq_nonneg (ρ - P - P * ρ),
      mul_le_mul_of_nonneg_right h (by linarith : (0:ℝ) ≤ 1 + ρ)]
  · have hc : 0 < max 0 (min 1 (xiI ρ P ψ)) := by rw [← hx1]; exact hx
    have hle : xiStar ρ P ψ ≤ xiI ρ P ψ := by rw [hx1]; exact clamp_le _ hc
    by_cases hPρ : 0 < P * ρ
    · obtain ⟨hP, hρ⟩ := pos_of_prod hP0 hρ0 hPρ
      rw [xiI_bridge ρ P ψ hPρ] at hle
      have := (DPHelp.xiI_le_iff ρ ψ P _ hρ hP hP1 h hx.le).1.1 hle
      linarith [DPHelp.conv_gen ρ ψ P (xiStar ρ P ψ)]
    · have h0 : P * ρ = 0 := le_antisymm (not_lt.mp hPρ) (mul_nonneg hP0 hρ0)
      have ha : 0 < P + (1 - P) * ρ := by
        by_contra hna
        push_neg at hna
        have hX : xiI ρ P ψ = 0 := by
          unfold xiI; rw [if_neg hPρ, if_neg (not_lt.mpr hna)]
        rw [hX] at hle; linarith
      have hk := xiI_corner_key ρ P ψ h0 ha hψ
      have e1 : (1 + ρ * xiStar ρ P ψ) * (1 - P + P * xiStar ρ P ψ) =
          1 - P + (P + (1 - P) * ρ) * xiStar ρ P ψ + (P * ρ) * xiStar ρ P ψ ^ 2 := by ring
      have e2 : (1 - P) * ρ + P + 2 * P * ρ * xiStar ρ P ψ =
          (P + (1 - P) * ρ) + 2 * (P * ρ) * xiStar ρ P ψ := by ring
      rw [e1, e2, h0]
      linarith [mul_le_mul_of_nonneg_left hle (mul_pos (mul_pos four_pos ha) hψ).le]

lemma C_gen (ρ P ψ x : ℝ) (hρ0 : 0 ≤ ρ) (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ)
    (hx0 : 0 < x) (hx1 : x ≤ 1)
    (h : 4 * ψ * ((1 + ρ * x) * (1 - P + P * x)) ≤ ((1 - P) * ρ + P + 2 * P * ρ * x) ^ 2) :
    x ≤ xiStar ρ P ψ := by
  rcases xs_cases_new ρ P ψ with ⟨_, hx⟩ | ⟨hD, hx⟩
  · rw [hx]; exact hx1
  · rw [hx]
    suffices hX : x ≤ xiI ρ P ψ from le_max_of_le_right (le_min hx1 hX)
    by_cases hPρ : 0 < P * ρ
    · obtain ⟨hP, hρ⟩ := pos_of_prod hP0 hρ0 hPρ
      rw [xiI_bridge ρ P ψ hPρ]
      exact (DPHelp.xiI_le_iff ρ ψ P x hρ hP hP1 hD hx0.le).1.2
        (by linarith [DPHelp.conv_gen ρ ψ P x])
    · have h0 : P * ρ = 0 := le_antisymm (not_lt.mp hPρ) (mul_nonneg hP0 hρ0)
      have e1 : (1 + ρ * x) * (1 - P + P * x) = 1 - P + (P + (1 - P) * ρ) * x + (P * ρ) * x ^ 2 := by
        ring
      have e2 : (1 - P) * ρ + P + 2 * P * ρ * x = (P + (1 - P) * ρ) + 2 * (P * ρ) * x := by ring
      rw [e1, e2, h0] at h
      by_cases ha : 0 < P + (1 - P) * ρ
      · have hk := xiI_corner_key ρ P ψ h0 ha hψ
        by_contra hc
        push_neg at hc
        have := mul_lt_mul_of_pos_left hc (mul_pos (mul_pos four_pos ha) hψ)
        linarith
      · exfalso
        have ha0 : P + (1 - P) * ρ = 0 :=
          le_antisymm (not_lt.mp ha) (add_nonneg hP0 (mul_nonneg (by linarith) hρ0))
        have hP : P = 0 := by linarith [mul_nonneg (by linarith : (0:ℝ) ≤ 1 - P) hρ0]
        rw [ha0, hP] at h
        linarith

lemma mono_xi_new (ρ ψ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hψ : 0 < ψ) :
    MonotoneOn (fun P => xiStar ρ P ψ) (Set.Icc 0 1) := by
  intro a ha b hb hab
  simp only
  by_cases hx : 0 < xiStar ρ a ψ
  · have hB := B_gen ρ a ψ hρ0 ha.1 ha.2 hψ hx
    have hD := Dmono ρ ψ a b (xiStar ρ a ψ) hρ0 hρ1 hψ.le ha.1 hab (xs_range_new ρ a ψ).1
      (xs_range_new ρ a ψ).2 hB
    exact C_gen ρ b ψ _ hρ0 (ha.1.trans hab) hb.2 hψ hx (xs_range_new ρ a ψ).2 hD
  · push_neg at hx
    exact hx.trans (xs_range_new ρ b ψ).1

/-! monotonicity of C* -/

lemma Kf_of (r q x P : ℝ) (hr : 0 < r) (hq : 0 < q) (hx : 2 * r * q * x = r ^ 2 - (1 - P)) :
    x * (r - q * x) = DPHelp.Kf r P q := by
  unfold DPHelp.Kf
  have hx' : x = (r ^ 2 - (1 - P)) / (2 * r * q) := by
    rw [eq_div_iff (by positivity)]; linarith
  rw [hx']
  field_simp
  ring

lemma Phi0_int (ψ P X : ℝ) (hψ : 0 < ψ) (hP : 0 < P) (hX : 0 ≤ X)
    (hk : 4 * P * ψ * X = P ^ 2 - 4 * ψ * (1 - P)) :
    X * DPHelp.gv 0 ψ P X = DPHelp.Kf (P / (2 * √ψ)) P (√ψ) := by
  have hq0 : 0 < √ψ := Real.sqrt_pos.mpr hψ
  have hq2 : √ψ ^ 2 = ψ := Real.sq_sqrt hψ.le
  have hw : 4 * ψ * (1 - P + P * X) = 4 * ψ * (P / (2 * √ψ)) ^ 2 := by
    rw [div_pow, mul_pow, hq2]; field_simp; linear_combination hk
  have hw' : 1 - P + P * X = (P / (2 * √ψ)) ^ 2 := mul_left_cancel₀ (by positivity) hw
  have hg : DPHelp.gv 0 ψ P X = P / (2 * √ψ) - √ψ * X := by
    unfold DPHelp.gv
    rw [show (1 + 0 * X) * (1 - P + P * X) = (P / (2 * √ψ)) ^ 2 by rw [← hw']; ring,
      Real.sqrt_sq (by positivity)]
  rw [hg]
  apply Kf_of _ _ _ _ (by positivity) hq0
  have : 2 * (P / (2 * √ψ)) * √ψ = P := by field_simp
  rw [this, ← hw']
  ring

lemma Phi_rho0 (ψ P1 P2 : ℝ) (hψ : 0 < ψ) (hP1 : 0 ≤ P1) (h12 : P1 < P2) (hP2 : P2 ≤ 1) :
    xiStar 0 P1 ψ * DPHelp.gv 0 ψ P1 (xiStar 0 P1 ψ) ≤
      xiStar 0 P2 ψ * DPHelp.gv 0 ψ P2 (xiStar 0 P2 ψ) := by
  have hq0 : 0 < √ψ := Real.sqrt_pos.mpr hψ
  have hq2 : √ψ ^ 2 = ψ := Real.sq_sqrt hψ.le
  have hxs : ∀ P, xiStar 0 P ψ = max 0 (min 1 (xiI 0 P ψ)) := fun P => by
    unfold xiStar; rw [if_neg (by rw [mul_zero]; exact not_le.mpr hψ)]
  have hmono : xiStar 0 P1 ψ ≤ xiStar 0 P2 ψ :=
    mono_xi_new 0 ψ le_rfl (by norm_num) hψ ⟨hP1, by linarith⟩ ⟨by linarith, hP2⟩ h12.le
  obtain ⟨hx20, hx21⟩ := xs_range_new 0 P2 ψ
  have hg2 : 0 ≤ DPHelp.gv 0 ψ P2 (xiStar 0 P2 ψ) := by
    have := gmax_new 0 P2 ψ le_rfl (by linarith) hP2 hψ 0 le_rfl zero_le_one
    rw [DPHelp.gv_zero] at this
    exact le_trans (Real.sqrt_nonneg _) this
  have hΦ2 := mul_nonneg hx20 hg2
  have hkey : ∀ P, 0 < P → 4 * P * ψ * xiI 0 P ψ = P ^ 2 - 4 * ψ * (1 - P) := fun P hP => by
    have := xiI_corner_key 0 P ψ (mul_zero P) (by rw [mul_zero, add_zero]; exact hP) hψ
    rw [mul_zero, add_zero] at this
    exact this
  rcases clamp_cases (xiI 0 P1 ψ) with ⟨hX, hc⟩ | ⟨hX, hc⟩ | ⟨hX0, hX1, hc⟩
  · rw [hxs P1, hc, zero_mul]; exact hΦ2
  · have h1 : xiStar 0 P1 ψ = 1 := by rw [hxs, hc]
    have h2 : xiStar 0 P2 ψ = 1 := le_antisymm hx21 (h1 ▸ hmono)
    rw [h1, h2, one_mul, one_mul, DPHelp.gv_one, DPHelp.gv_one]
  · have hP1p : 0 < P1 := by
      rcases eq_or_lt_of_le hP1 with h | h
      · exfalso
        rw [← h] at hX0
        unfold xiI at hX0
        simp at hX0
      · exact h
    have hk1 := hkey P1 hP1p
    have hx1 : xiStar 0 P1 ψ = xiI 0 P1 ψ := by rw [hxs, hc]
    have hx1p : 0 < xiStar 0 P1 ψ := by rw [hx1]; exact hX0
    rw [hx1, Phi0_int ψ P1 _ hψ hP1p hX0.le hk1]
    have hr1 : 0 < P1 / (2 * √ψ) := by positivity
    have hsq1 : P1 ^ 2 < 4 * ψ := by
      linarith [mul_lt_mul_of_pos_left hX1 (mul_pos (mul_pos four_pos hP1p) hψ)]
    have hP1q : P1 < 2 * √ψ := by
      by_contra hc
      push_neg at hc
      have := pow_le_pow_left₀ (by positivity) hc 2
      rw [mul_pow, hq2] at this
      linarith
    have hN : 1 - P1 < (P1 / (2 * √ψ)) ^ 2 := by
      rw [div_pow, mul_pow, hq2, lt_div_iff₀ (by positivity)]
      linarith [mul_pos (mul_pos hP1p hψ) hX0]
    have hx2pos : 0 < xiStar 0 P2 ψ := lt_of_lt_of_le hx1p hmono
    have hP2p : 0 < P2 := by linarith
    have hk2 := hkey P2 hP2p
    rcases clamp_cases (xiI 0 P2 ψ) with ⟨hY, hc2⟩ | ⟨hY, hc2⟩ | ⟨hY0, hY1, hc2⟩
    · exfalso; rw [hxs, hc2] at hx2pos; exact lt_irrefl _ hx2pos
    · have h2 : xiStar 0 P2 ψ = 1 := by rw [hxs, hc2]
      rw [h2, one_mul, DPHelp.gv_one, add_zero, Real.sqrt_one]
      have hsq2 : 4 * ψ ≤ P2 ^ 2 := by
        linarith [mul_le_mul_of_nonneg_left hY (mul_pos (mul_pos four_pos hP2p) hψ).le]
      have hP2q : 2 * √ψ ≤ P2 :=
        DPHelp.sq_le_imp hP2p.le (by rw [mul_pow, hq2]; linarith)
      have e := Kf_of 1 (√ψ) 1 (2 * √ψ) one_pos hq0 (by ring)
      rw [show (1:ℝ) - √ψ = 1 * (1 - √ψ * 1) by ring, e]
      unfold DPHelp.Kf
      exact DPHelp.mono_pos_alg _ _ _ _ _ _ hr1 ((div_le_one (by positivity)).mpr hP1q.le) hq0
        le_rfl (by linarith) (by linarith) hN
    · have h2 : xiStar 0 P2 ψ = xiI 0 P2 ψ := by rw [hxs, hc2]
      rw [h2, Phi0_int ψ P2 _ hψ hP2p hY0.le hk2]
      unfold DPHelp.Kf
      exact DPHelp.mono_pos_alg _ _ _ _ _ _ hr1
        (div_le_div_of_nonneg_right h12.le (by positivity)) hq0 le_rfl (by linarith)
        (by linarith) hN

lemma Kn0_mono (ρ ψ P' : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hψ : 0 < ψ) (hP' : 0 < P')
    (hD : P' * ρ < ψ) (hd : P' - (1 - P') * ρ < 0) (h4 : 4 * ψ < ρ ^ 2) :
    DPHelp.Kf (2 * √ψ / ρ) 0 (-√ψ) ≤ DPHelp.Kf (DPHelp.rn ρ ψ P') P' (-√(ψ - P' * ρ)) := by
  obtain ⟨hr, hq, -, -⟩ := DPHelp.branch_neg ρ ψ P' hρ0 hP' hD hd
  have hq0 : 0 < √ψ := Real.sqrt_pos.mpr hψ
  have hq2 : √ψ ^ 2 = ψ := Real.sq_sqrt hψ.le
  have hρne : ρ ≠ 0 := hρ0.ne'
  have hs2 : 0 < √(ψ - P' * ρ) := Real.sqrt_pos.mpr (by linarith)
  have hs12 : √(ψ - P' * ρ) ≤ √ψ := Real.sqrt_le_sqrt (by linarith [mul_pos hP' hρ0])
  have hr21 : DPHelp.rn ρ ψ P' ≤ 2 * √ψ / ρ := by
    unfold DPHelp.rn
    apply div_le_div_of_nonneg_right _ hρ0.le
    linarith
  have hN : (2 * √ψ / ρ) ^ 2 < 1 - 0 := by
    rw [div_pow, mul_pow, hq2, sub_zero, div_lt_one (by positivity)]
    linarith
  unfold DPHelp.Kf
  exact DPHelp.mono_neg_alg _ _ _ _ _ _ ρ (√ψ) hρ1 hρ0 hr hr21 hs2 hs12
    (by field_simp; ring) (by linarith) hN (by norm_num)

lemma Phi_P0 (ρ ψ P2 : ℝ) (hρ0 : 0 < ρ) (hρ1 : ρ < 1) (hψ : 0 < ψ) (hP2 : 0 < P2)
    (hP21 : P2 ≤ 1) :
    xiStar ρ 0 ψ * DPHelp.gv ρ ψ 0 (xiStar ρ 0 ψ) ≤
      xiStar ρ P2 ψ * DPHelp.gv ρ ψ P2 (xiStar ρ P2 ψ) := by
  have hmono : xiStar ρ 0 ψ ≤ xiStar ρ P2 ψ :=
    mono_xi_new ρ ψ hρ0.le hρ1 hψ ⟨le_rfl, zero_le_one⟩ ⟨hP2.le, hP21⟩ hP2.le
  have hb := xs_bridge ρ P2 ψ (mul_pos hP2 hρ0)
  rw [hb] at hmono ⊢
  obtain ⟨hx20, hx21⟩ := DPHelp.xs_range ρ ψ P2
  have hg2 := DPHelp.g_nonneg ρ ψ P2 hρ0 hψ hP2 hP21
  have hΦ2 := mul_nonneg hx20 hg2
  have hxs : xiStar ρ 0 ψ = max 0 (min 1 (xiI ρ 0 ψ)) := by
    unfold xiStar; rw [if_neg (by rw [zero_mul]; exact not_le.mpr hψ)]
  have hk : 4 * ρ * ψ * xiI ρ 0 ψ = ρ ^ 2 - 4 * ψ := by
    have := xiI_corner_key ρ 0 ψ (zero_mul ρ) (by rw [sub_zero, one_mul, zero_add]; exact hρ0) hψ
    rw [sub_zero, one_mul, zero_add, mul_one] at this
    exact this
  rcases clamp_cases (xiI ρ 0 ψ) with ⟨hX, hc⟩ | ⟨hX, hc⟩ | ⟨hX0, hX1, hc⟩
  · rw [hxs, hc, zero_mul]; exact hΦ2
  · have h1 : xiStar ρ 0 ψ = 1 := by rw [hxs, hc]
    have h2 : DigitalPrivacy.Strategy.xiStar ρ ψ P2 = 1 := le_antisymm hx21 (h1 ▸ hmono)
    rw [h1, h2, one_mul, one_mul, DPHelp.gv_one, DPHelp.gv_one]
  · have hx1 : xiStar ρ 0 ψ = xiI ρ 0 ψ := by rw [hxs, hc]
    have hx1p : 0 < xiStar ρ 0 ψ := by rw [hx1]; exact hX0
    rw [hx1]
    have hq0 : 0 < √ψ := Real.sqrt_pos.mpr hψ
    have hq2 : √ψ ^ 2 = ψ := Real.sq_sqrt hψ.le
    have h4 : 4 * ψ < ρ ^ 2 := by linarith [mul_pos (mul_pos hρ0 hψ) hX0]
    have h5 : ρ ^ 2 < 4 * ψ * (1 + ρ) := by
      linarith [mul_lt_mul_of_pos_left hX1 (by positivity : (0:ℝ) < 4 * ρ * ψ)]
    have hρne : ρ ≠ 0 := hρ0.ne'
    have hqne : √ψ ≠ 0 := hq0.ne'
    have hΦ1 : xiI ρ 0 ψ * DPHelp.gv ρ ψ 0 (xiI ρ 0 ψ) = DPHelp.Kf (2 * √ψ / ρ) 0 (-√ψ) := by
      apply DPHelp.K_formula ρ ψ 0 _ _ _ hρ0 hX0.le (by positivity) (neg_ne_zero.mpr hqne)
      · field_simp; ring
      · field_simp; ring
      · have hX : xiI ρ 0 ψ = (ρ ^ 2 - 4 * ψ) / (4 * ρ * ψ) := by
          rw [eq_div_iff (by positivity)]; linarith [hk]
        rw [hX]
        obtain ⟨q, hq⟩ : ∃ q, q = √ψ := ⟨_, rfl⟩
        rw [← hq]
        have hq2' : q ^ 2 = ψ := by rw [hq]; exact hq2
        have hqne' : q ≠ 0 := by rw [hq]; exact hqne
        subst hq2'
        field_simp
        ring
    rw [hΦ1]
    have hPm : ψ * (1 + ρ) < ρ ^ 2 := by
      linarith [mul_lt_mul_of_pos_left hρ1 hψ, sq_nonneg ρ]
    rcases eq_or_lt_of_le hx21 with h2 | h2
    · rw [h2, one_mul, DPHelp.gv_one]
      have hW := DPHelp.W_sq ρ ψ hρ0 hψ
      obtain ⟨P0, hP0d⟩ : ∃ P0 : ℝ, ρ + P0 * (1 + ρ) = 2 * √ψ * √(1 + ρ) :=
        ⟨(2 * √ψ * √(1 + ρ) - ρ) / (1 + ρ), by rw [div_mul_cancel₀ _ (by positivity)]; ring⟩
      have hP0sq : (ρ + P0 * (1 + ρ)) ^ 2 = 4 * ψ * (1 + ρ) := by rw [hP0d, hW]
      have hP0pos : 0 < P0 := by
        have hlt : ρ < ρ + P0 * (1 + ρ) := by
          by_contra hc
          push_neg at hc
          have h0' : 0 ≤ ρ + P0 * (1 + ρ) := by rw [hP0d]; positivity
          linarith [mul_self_le_mul_self h0' hc]
        by_contra hc0
        push_neg at hc0
        linarith [mul_le_mul_of_nonneg_right hc0 (by linarith : (0:ℝ) ≤ 1 + ρ)]
      have hqw : √ψ * √(1 + ρ) < ρ := by
        by_contra hc
        push_neg at hc
        have := mul_self_le_mul_self hρ0.le hc
        linarith [hW]
      have hd0 : P0 - (1 - P0) * ρ < 0 := by linarith [hP0d]
      have hD0 : P0 * ρ < ψ := by
        have e : 4 * (1 + ρ) * (ψ - P0 * ρ) = (P0 - (1 - P0) * ρ) ^ 2 := by
          linear_combination (-1) * hP0sq
        have : 0 < (P0 - (1 - P0) * ρ) ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hd0.ne))
        by_contra hc
        push_neg at hc
        have : 4 * (1 + ρ) * (ψ - P0 * ρ) ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
        linarith
      have hP01 : P0 ≤ 1 := by
        by_contra hc
        push_neg at hc
        have hρψ : ρ < ψ := by linarith [mul_lt_mul_of_pos_right hc hρ0]
        linarith [mul_lt_mul_of_pos_right hρψ hρ0]
      have hy0e : DigitalPrivacy.Strategy.xiI ρ ψ P0 = 1 := by
        have hk' := DPHelp.xiI_le_iff ρ ψ P0 1 hρ0 hP0pos hP01 hD0 zero_le_one
        have e := DPHelp.conv1 ρ ψ P0
        apply le_antisymm
        · by_contra hc
          push_neg at hc
          have := hk'.2.1 hc
          linarith
        · apply hk'.1.2; linarith
      have hK0 := DPHelp.Kn_eq ρ ψ P0 hρ0 hP0pos hD0 hd0 (by rw [hy0e]; exact zero_le_one)
      rw [hy0e, one_mul, DPHelp.gv_one] at hK0
      rw [hK0]
      exact Kn0_mono ρ ψ P0 hρ0 hρ1 hψ hP0pos hD0 hd0 h4
    · obtain ⟨hD2, hξ2e, hy2p, _⟩ :=
        DPHelp.interior_extract ρ ψ P2 (lt_of_lt_of_le hx1p hmono) h2
      have hd2 : P2 - (1 - P2) * ρ < 0 := by
        by_contra hc
        push_neg at hc
        linarith [mul_le_mul_of_nonneg_left hc hρ0.le,
          mul_lt_mul_of_pos_right hD2 (by linarith : (0:ℝ) < 1 + ρ)]
      rw [hξ2e, DPHelp.Kn_eq ρ ψ P2 hρ0 hP2 hD2 hd2 hy2p.le]
      exact Kn0_mono ρ ψ P2 hρ0 hρ1 hψ hP2 hD2 hd2 h4

lemma Phi_new (ρ ψ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hψ : 0 < ψ) :
    MonotoneOn (fun P => xiStar ρ P ψ * DPHelp.gv ρ ψ P (xiStar ρ P ψ)) (Set.Icc 0 1) := by
  intro a ha b hb hab
  simp only
  rcases eq_or_lt_of_le hab with h | h
  · rw [h]
  rcases eq_or_lt_of_le hρ0 with hρ | hρ
  · subst hρ; exact Phi_rho0 ψ a b hψ ha.1 h hb.2
  rcases eq_or_lt_of_le ha.1 with ha0 | ha0
  · subst ha0; exact Phi_P0 ρ ψ b hρ hρ1 hψ h hb.2
  · rw [xs_bridge ρ a ψ (mul_pos ha0 hρ), xs_bridge ρ b ψ (mul_pos (ha0.trans h) hρ)]
    exact DPHelp.Phi_mono ρ ψ a b hρ hρ1 hψ ha0 h hb.2

lemma mono_cstar_new (β ρ ψ : ℝ) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hψ : 0 < ψ) :
    MonotoneOn (fun P => cStar β ρ P ψ) (Set.Icc 0 1) := by
  intro a ha b hb hab
  simp only
  rw [cStar_eq, cStar_eq, cH_formula _ _ _ _ _ hψ hβ1, cH_formula _ _ _ _ _ hψ hβ1]
  exact div_le_div_of_nonneg_right (Phi_new ρ ψ hρ0 hρ1 hψ ha hb hab)
    (mul_pos (Real.sqrt_pos.mpr hψ) (by linarith)).le

end DPNew

open DigitalPrivacy.DataStrategy in
theorem solution {β ρ P ψ : ℝ}
    (hβ0 : 0 ≤ β) (hβ1 : β < 1) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hP0 : 0 ≤ P) (hP1 : P ≤ 1) (hψ : 0 < ψ) :
    IsBusinessOptimal β ρ P ψ (xiStar ρ P ψ) (cStar β ρ P ψ) ∧
    (¬ (P * (1 + ρ) = ρ ∧ ψ = P * ρ) →
      ∀ ξ C : ℝ, IsBusinessOptimal β ρ P ψ ξ C ↔ ξ = xiStar ρ P ψ ∧ C = cStar β ρ P ψ) ∧
    (P * (1 + ρ) = ρ ∧ ψ = P * ρ →
      ∀ ξ C : ℝ, IsBusinessOptimal β ρ P ψ ξ C ↔ ξ ∈ Set.Icc (0 : ℝ) 1 ∧ C = cH β ρ P ψ ξ) ∧
    MonotoneOn (fun P' => xiStar ρ P' ψ) (Set.Icc 0 1) ∧
    MonotoneOn (fun P' => cStar β ρ P' ψ) (Set.Icc 0 1) := by
  have hr := DPNew.xs_range_new ρ P ψ
  have hxs : xiStar ρ P ψ ∈ Set.Icc (0 : ℝ) 1 := ⟨hr.1, hr.2⟩
  have hmax : ∀ y ∈ Set.Icc (0 : ℝ) 1,
      DPHelp.gv ρ ψ P y ≤ DPHelp.gv ρ ψ P (xiStar ρ P ψ) :=
    fun y hy => DPNew.gmax_new ρ P ψ hρ0 hP0 hP1 hψ y hy.1 hy.2
  have hpos := DPNew.gpos ρ P ψ hρ0 hP0 hP1 hψ
  have hopt := DPNew.opt_iff β ρ P ψ (xiStar ρ P ψ) hβ1 hρ0 hP0 hP1 hψ hxs hmax hpos
  have hcs := DPNew.cStar_eq β ρ P ψ
  refine ⟨?_, ?_, ?_, DPNew.mono_xi_new ρ ψ hρ0 hρ1 hψ,
    DPNew.mono_cstar_new β ρ ψ hβ1 hρ0 hρ1 hψ⟩
  · rw [hopt, hcs]
    exact ⟨⟨hxs, hmax⟩, rfl⟩
  · intro hnk ξ C
    rw [hopt, hcs]
    constructor
    · rintro ⟨⟨hξ, hξm⟩, hC⟩
      have he := DPNew.uniq ρ ψ P ξ (xiStar ρ P ψ) hρ0 hP0 hP1 hψ hnk hξ hxs hξm hmax
      exact ⟨he, by rw [hC, he]⟩
    · rintro ⟨rfl, rfl⟩
      exact ⟨⟨hxs, hmax⟩, rfl⟩
  · rintro ⟨hk, hψe⟩ ξ C
    rw [hopt]
    constructor
    · rintro ⟨⟨hξ, _⟩, hC⟩
      exact ⟨hξ, hC⟩
    · rintro ⟨hξ, hC⟩
      refine ⟨⟨hξ, fun y hy => ?_⟩, hC⟩
      rw [DPNew.knife ρ ψ P y hP1 hρ0 hy.1 hk hψe, DPNew.knife ρ ψ P ξ hP1 hρ0 hξ.1 hk hψe]
