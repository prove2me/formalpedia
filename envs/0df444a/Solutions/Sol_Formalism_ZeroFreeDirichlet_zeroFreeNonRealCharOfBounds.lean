-- Prove2me | solution 1 for Formalism.ZeroFreeDirichlet.zeroFreeNonRealCharOfBounds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:59:10.428015+00:00
-- url     : https://prove2.me/submissions/fc5f7a6b-4007-4d32-8c77-e899b37752ca

import Definitions.Def_Formalism_LandauZeroFreeBounds_NoZeroComplexOf
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_NoZeroComplexOf
import Theorems.Thm_Formalism_ZeroFreeDirichlet_re_one_div_sub_zero_pos_ter
import Theorems.Thm_Formalism_ZeroFreeDirichlet_sum_mult_re_one_div_sub_zeros_nonneg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Complex
noncomputable section
open Formalism Formalism.ZeroFreeDirichlet
set_option maxHeartbeats 1000000
namespace Formalism.ZeroFreeDirichlet
theorem _root_.solution : NoZeroComplexOf := by
  unfold NoZeroComplexOf LocalZeros LLogDerivRight Positivity NoZeroComplex InRegion
  intro hLZ hLD hPos
  obtain ⟨C0, hC0⟩ := hLZ
  obtain ⟨C1, hC1nn, hC1⟩ := hLD
  set K : ℝ := |C0| with hK
  have hKnn : 0 ≤ K := abs_nonneg _
  set A : ℝ := 6 * K + 5 * C1 + 1 with hA
  have hApos : 0 < A := by rw [hA]; linarith
  set δ : ℝ := min (1 / 10) (1 / (2 * A)) with hδ
  have hδpos : 0 < δ := lt_min (by norm_num) (by positivity)
  have hδ1 : δ ≤ 1 / 10 := min_le_left _ _
  have hδ2 : δ ≤ 1 / (2 * A) := min_le_right _ _
  refine ⟨δ / 8, by positivity, ?_⟩
  intro q _ χ s hχ2 hreg hzero
  have hχ : χ ≠ 1 := fun h => hχ2 (by rw [h, one_pow])
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set ℓ := Real.log ((q : ℝ) * (|s.im| + 2)) with hℓ
  have hlog2 : Real.log 2 ≤ ℓ :=
    Real.log_le_log (by norm_num) (by nlinarith [abs_nonneg s.im])
  have hl2 : (0.69 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    norm_num at this ⊢
    linarith
  have hℓ69 : (0.69 : ℝ) < ℓ := lt_of_lt_of_le hl2 hlog2
  have hℓpos : 0 < ℓ := by linarith
  have hβ1 : s.re < 1 := by
    by_contra h
    push_neg at h
    exact DirichletCharacter.LFunction_ne_zero_of_one_le_re χ (Or.inl hχ) h hzero
  have hsmall : δ / 8 / ℓ ≤ 1 / 10 := by
    rw [div_le_iff₀ hℓpos]
    linarith
  have hβ9 : 9 / 10 ≤ s.re := by linarith
  set σ : ℝ := 1 + δ / ℓ with hσ
  have hvpos : 0 < δ / ℓ := div_pos hδpos hℓpos
  have hσ1 : 1 < σ := by linarith
  have hσ2 : σ ≤ 6 / 5 := by
    have : δ / ℓ ≤ 1 / 5 := by
      rw [div_le_iff₀ hℓpos]
      linarith
    linarith
  set u : ℝ := 1 / δ with hu

  have b0 : (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ)).re ≤ ℓ * u + C1 := by
    have h1 := hC1 q 1 (σ : ℂ) (by simpa using hσ1)
    have h2 := Complex.re_le_norm (negLD (1 : DirichletCharacter ℂ q) (σ : ℂ))
    have h3 : 1 / ((σ : ℂ).re - 1) = ℓ * u := by
      rw [Complex.ofReal_re, hσ, hu, add_sub_cancel_left, one_div_div, div_eq_mul_one_div]
    rw [h3] at h1
    linarith

  obtain ⟨Z, m, hZ, hm1, -, hbd⟩ := hC0 q χ hχ s.im
  have hsZ : s ∈ Z := by
    refine (hZ s).mpr ⟨?_, hzero⟩
    have e : s - ((11 / 10 : ℂ) + s.im * I) = ((s.re - 11 / 10 : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    rw [mem_closedBall_iff_norm, e, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor <;> linarith
  have hterm : 1 / (σ - s.re) ≤ (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re := by
    have e : (σ : ℂ) + s.im * I - s = ((σ - s.re : ℝ) : ℂ) := by
      apply Complex.ext <;> simp
    have e2 : (1 / ((σ - s.re : ℝ) : ℂ)).re = 1 / (σ - s.re) := by
      rw [← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
    rw [e, e2]
    have hm : (1 : ℝ) ≤ (m s : ℝ) := by exact_mod_cast hm1 s hsZ
    have hpos : 0 < 1 / (σ - s.re) := by apply div_pos one_pos; linarith
    nlinarith
  have hsum : (m s : ℝ) * (1 / ((σ : ℂ) + s.im * I - s)).re ≤
      ∑ ρ ∈ Z, (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re :=
    Finset.single_le_sum (f := fun ρ => (m ρ : ℝ) * (1 / ((σ : ℂ) + s.im * I - ρ)).re)
      (fun ρ hρ => mul_nonneg (Nat.cast_nonneg _)
        (re_one_div_sub_zero_pos_ter χ hχ ρ ((hZ ρ).mp hρ).2 σ s.im hσ1).le) hsZ
  have hgap : σ - s.re ≤ (9 / 8) * (δ / ℓ) := by
    have : δ / 8 / ℓ = (δ / ℓ) / 8 := by ring
    rw [hσ]
    linarith
  have hgappos : 0 < σ - s.re := by linarith
  have hinv : (8 / 9) * (ℓ * u) ≤ 1 / (σ - s.re) := by
    have h1 := one_div_le_one_div_of_le hgappos hgap
    have h2 : 1 / ((9 / 8) * (δ / ℓ)) = (8 / 9) * (ℓ * u) := by
      rw [hu]
      field_simp
    linarith
  have b1 : (negLD χ ((σ : ℂ) + s.im * I)).re ≤ K * ℓ - (8 / 9) * (ℓ * u) := by
    have h1 := hbd σ hσ1 hσ2
    rw [← hℓ] at h1
    have h2 : C0 * ℓ ≤ K * ℓ := mul_le_mul_of_nonneg_right (le_abs_self C0) hℓpos.le
    linarith

  obtain ⟨Z2, m2, hZ2, -, -, hbd2⟩ := hC0 q (χ ^ 2) hχ2 (2 * s.im)
  have hL2 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ 2 * ℓ := by
    have ha := abs_nonneg s.im
    have h1 : Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ Real.log (((q : ℝ) * (|s.im| + 2)) ^ 2) := by
      apply Real.log_le_log
      · rw [abs_mul, abs_two]
        positivity
      · rw [abs_mul, abs_two]
        nlinarith [mul_le_mul_of_nonneg_right hq (sq_nonneg (|s.im| + 2))]
    rw [Real.log_pow] at h1
    push_cast at h1
    linarith
  have hL2nn : 0 ≤ Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
    Real.log_nonneg (by nlinarith [abs_nonneg (2 * s.im)])
  have b2 : (negLD (χ ^ 2) ((σ : ℂ) + 2 * s.im * I)).re ≤ 2 * (K * ℓ) := by
    have h1 := hbd2 σ hσ1 hσ2
    push_cast at h1
    have h2 := sum_mult_re_one_div_sub_zeros_nonneg (χ ^ 2) hχ2 Z2 m2 (fun ρ hρ => ((hZ2 ρ).mp hρ).2) σ (2 * s.im) hσ1
    push_cast at h2
    have h3 : C0 * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) :=
      mul_le_mul_of_nonneg_right (le_abs_self C0) hL2nn
    have h4 : K * Real.log ((q : ℝ) * (|2 * s.im| + 2)) ≤ K * (2 * ℓ) :=
      mul_le_mul_of_nonneg_left hL2 hKnn
    have h5 : K * (2 * ℓ) = 2 * (K * ℓ) := by ring
    linarith

  have hP := (hPos q σ hσ1).1 χ s.im
  have hu2 : 2 * A ≤ u := by
    have h1 := one_div_le_one_div_of_le hδpos hδ2
    rw [one_div_one_div] at h1
    exact h1
  have cu : 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ ≤ ℓ * u := by
    have h1 := mul_le_mul_of_nonneg_left hu2 hℓpos.le
    have e : ℓ * (2 * A) = 12 * (K * ℓ) + 10 * (C1 * ℓ) + 2 * ℓ := by rw [hA]; ring
    linarith
  have c1 : 3 * C1 ≤ 5 * (C1 * ℓ) := by
    have := mul_le_mul_of_nonneg_left hℓ69.le hC1nn
    linarith
  have hKl : 0 ≤ K * ℓ := mul_nonneg hKnn hℓpos.le
  have hCl : 0 ≤ C1 * ℓ := mul_nonneg hC1nn hℓpos.le
  linarith
end Formalism.ZeroFreeDirichlet
