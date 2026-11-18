-- Prove2me | solution 1 for CritWinSpin.sampler_smoothed_cap_budget
-- status  : ACCEPTED   (prove)
-- author  : @Maxliu
-- created : 2026-11-17T11:28:23.658104+00:00
-- url     : https://prove2.me/submissions/18c44c97-b942-4883-86e1-04d4f6f43fe2

import Mathlib
import Theorems.Thm_CritWinSpin_lemma_4_2
import Theorems.Thm_CritWinSpin_p4c_4_4_ula_math

set_option autoImplicit false

open CritWinSpin

theorem solution (S : SpinLaw) (p : ℕ) (hS : IsGHS S) (hp : IsTypeP S p) :
    ∃ D : ℝ, 0 < D ∧ ∀ (N m : ℕ) (δ : ℝ), 5 ≤ m → 0 ≤ δ →
      (N : ℝ) * deltaS S
          (tau S * (1 + δ) + 1 / ((m : ℝ) * ((N : ℝ) + 1))) + 1 ≤
        D * ((N : ℝ) * δ ^ ((p : ℝ) / ((p : ℝ) - 1)) + 1) := by
  have htau : 1 ≤ tau S := p4c_4_4_ula_math.{0}.1 S
  have htau0 : 0 ≤ tau S := by linarith
  have hpr : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.1
  have hpden : 0 < (p : ℝ) - 1 := by linarith
  let r : ℝ := (p : ℝ) / ((p : ℝ) - 1)
  have hr : 1 ≤ r := by
    dsimp [r]
    rw [le_div_iff₀ hpden]
    linarith
  have hr0 : 0 ≤ r := by linarith
  obtain ⟨C, hC, hcap⟩ := lemma_4_2 S p hS hp
  let A : ℝ := C * (tau S + 1) ^ r
  have htau1 : 0 ≤ tau S + 1 := by linarith
  have hA : 0 ≤ A := mul_nonneg hC.le (Real.rpow_nonneg htau1 r)
  refine ⟨A + 1, by positivity, ?_⟩
  intro N m δ hm hδ
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hm5 : (5 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hmpos : 0 < (m : ℝ) := by linarith
  let e : ℝ := 1 / ((m : ℝ) * ((N : ℝ) + 1))
  let s : ℝ := tau S * (1 + δ) + e
  have hden : 0 < (m : ℝ) * ((N : ℝ) + 1) := by positivity
  have he : 0 < e := by dsimp [e]; positivity
  have he1 : e ≤ 1 := by
    dsimp [e]
    rw [div_le_one hden]
    nlinarith
  have hNe : (N : ℝ) * e ≤ 1 := by
    dsimp [e]
    rw [mul_one_div, div_le_iff₀ hden]
    nlinarith
  have hNer : (N : ℝ) * e ^ r ≤ 1 :=
    (mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one he.le he1 hr) hN).trans hNe
  have hs : tau S < s := by
    dsimp [s]
    nlinarith [mul_nonneg htau0 hδ]
  obtain ⟨_, _, _, _, _, _, hDelta⟩ := hcap s hs
  have hsm : s - tau S = tau S * δ + e := by dsimp [s]; ring
  have hsm0 : 0 ≤ s - tau S := by linarith
  have hδr : 0 ≤ δ ^ r := Real.rpow_nonneg hδ r
  let X : ℝ := (N : ℝ) * δ ^ r
  have hX : 0 ≤ X := mul_nonneg hN hδr
  change (N : ℝ) * deltaS S s + 1 ≤ (A + 1) * (X + 1)
  by_cases hcomp : e ≤ δ
  · have hsδ : s - tau S ≤ (tau S + 1) * δ := by rw [hsm]; nlinarith
    have hDδ : deltaS S s ≤ A * δ ^ r := by
      calc
        deltaS S s ≤ C * (s - tau S) ^ r := hDelta
        _ ≤ C * ((tau S + 1) * δ) ^ r :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hsm0 hsδ hr0) hC.le
        _ = A * δ ^ r := by rw [Real.mul_rpow htau1 hδ]; dsimp [A]; ring
    have hND : (N : ℝ) * deltaS S s ≤ A * X := by
      simpa only [X, mul_assoc, mul_left_comm, mul_comm] using
        mul_le_mul_of_nonneg_left hDδ hN
    nlinarith
  · have hδe : δ ≤ e := (lt_of_not_ge hcomp).le
    have hse : s - tau S ≤ (tau S + 1) * e := by
      rw [hsm]
      nlinarith [mul_le_mul_of_nonneg_left hδe (by linarith : 0 ≤ tau S)]
    have hDe : deltaS S s ≤ A * e ^ r := by
      calc
        deltaS S s ≤ C * (s - tau S) ^ r := hDelta
        _ ≤ C * ((tau S + 1) * e) ^ r :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hsm0 hse hr0) hC.le
        _ = A * e ^ r := by rw [Real.mul_rpow htau1 he.le]; dsimp [A]; ring
    have hND : (N : ℝ) * deltaS S s ≤ A := by
      calc
        (N : ℝ) * deltaS S s ≤ (N : ℝ) * (A * e ^ r) :=
          mul_le_mul_of_nonneg_left hDe hN
        _ = A * ((N : ℝ) * e ^ r) := by ring
        _ ≤ A * 1 := mul_le_mul_of_nonneg_left hNer hA
        _ = A := by ring
    nlinarith [mul_nonneg hA hX]
