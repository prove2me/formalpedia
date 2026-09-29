-- Prove2me | solution 1 for EulerMascheroni.Mixed.expEin_one_not_mem_rat_exp_span
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T21:19:45.546298+00:00
-- url     : https://prove2.me/submissions/12c2b5ee-d103-455c-947d-fef523dcd8c9

import Theorems.Thm_LinearForms_not_mem_rat_span_of_nonvanishing_forms
import Theorems.Thm_EulerMascheroni_Rivoal_linear_form_identity
import Theorems.Thm_EulerMascheroni_Rivoal_pCoef_isInt
import Theorems.Thm_EulerMascheroni_Rivoal_rCoef_isInt
import Theorems.Thm_EulerMascheroni_Rivoal_den_mul_qCoef_isInt
import Theorems.Thm_EulerMascheroni_Rivoal_remainder_bounds
import Theorems.Thm_EulerMascheroni_Rivoal_height_bound
import Theorems.Thm_EulerMascheroni_Rivoal_den_le
import Definitions.Def_eulerMascheroni_mixedCover
import Mathlib.Topology.Algebra.Order.Floor
import Mathlib.Analysis.SpecialFunctions.Exp

open Filter Topology EulerMascheroni.Rivoal

namespace RivoalAssembly

lemma rCoef_pos (n : ℕ) : 0 < rCoef n := by
  unfold rCoef
  apply Finset.sum_pos
  · intro j _
    unfold beta
    positivity
  · exact ⟨0, by simp⟩

lemma den_pos (n : ℕ) : 0 < den n := by
  unfold den
  apply Nat.pos_of_ne_zero
  rw [Ne, Finset.lcm_eq_zero_iff]
  simp

lemma exp_one_eq : Complex.exp 1 = ((Real.exp 1 : ℝ) : ℂ) := by
  rw [Complex.ofReal_exp]; simp

lemma expEin_real :
    EulerMascheroni.Mixed.expEin 1 = (((EulerMascheroni.Mixed.expEin 1).re : ℝ) : ℂ) := by
  have h := linear_form_identity 1 le_rfl
  rw [exp_one_eq] at h
  have him := congrArg Complex.im h
  simp only [Complex.add_im, Complex.mul_im, Complex.ratCast_re, Complex.ratCast_im,
    Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_mul, add_zero, zero_add] at him
  have hr := rCoef_pos 1
  apply Complex.ext
  · simp
  · rcases mul_eq_zero.mp him with h' | h'
    · exact absurd (by exact_mod_cast h') hr.ne'
    · simp [h']

lemma real_identity (n : ℕ) (hn : 1 ≤ n) :
    (pCoef n : ℝ) + (qCoef n : ℝ) * Real.exp 1
      + (rCoef n : ℝ) * (EulerMascheroni.Mixed.expEin 1).re
      = Real.exp 1 * remainder n := by
  have h := linear_form_identity n hn
  rw [expEin_real, exp_one_eq] at h
  exact_mod_cast h

lemma poly_le (n : ℕ) : (9 * (n : ℝ) + 1) ≤ 10 * 2 ^ n := by
  induction n with
  | zero => norm_num
  | succ k ih => push_cast; rw [pow_succ]; linarith [one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := k)]

lemma den_le' (n : ℕ) : (den n : ℝ) ≤ 1331 ^ n := by
  have := den_le n
  rw [pow_mul] at this
  norm_num at this
  exact this

/-- `A n := den n · e · S n` is positive and small. -/
lemma A_bounds (n : ℕ) :
    0 < (den n : ℝ) * (Real.exp 1 * remainder n) ∧
      (den n : ℝ) * (Real.exp 1 * remainder n)
        ≤ Real.exp 1 * 1331 ^ n / (((n + 1).factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
  obtain ⟨hS0, hS1⟩ := remainder_bounds n
  have hd : (0 : ℝ) < den n := by exact_mod_cast den_pos n
  have hE := Real.exp_pos 1
  refine ⟨by positivity, ?_⟩
  have hF : (0 : ℝ) < ((n + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
  calc (den n : ℝ) * (Real.exp 1 * remainder n)
      ≤ 1331 ^ n * (Real.exp 1 * (1 / ((n + 1).factorial : ℝ) ^ 2)) :=
        mul_le_mul (den_le' n) (mul_le_mul_of_nonneg_left hS1 hE.le) (by positivity)
          (by positivity)
    _ = Real.exp 1 * 1331 ^ n / (((n + 1).factorial : ℝ) * ((n + 1).factorial : ℝ)) := by
        field_simp

end RivoalAssembly

open RivoalAssembly in
theorem solution (α β : ℚ) :
    EulerMascheroni.Mixed.expEin 1 ≠ (α : ℂ) + (β : ℂ) * Complex.exp 1 := by
  set θ := (EulerMascheroni.Mixed.expEin 1).re with hθ
  have hp : ∀ k : ℕ, ∃ z : ℤ, (den (k + 1) : ℚ) * pCoef (k + 1) = z := fun k => by
    obtain ⟨z, hz⟩ := pCoef_isInt (k + 1) (by omega)
    exact ⟨den (k + 1) * z, by rw [hz]; push_cast; ring⟩
  have hq : ∀ k : ℕ, ∃ z : ℤ, (den (k + 1) : ℚ) * qCoef (k + 1) = z := fun k =>
    den_mul_qCoef_isInt (k + 1)
  have hr : ∀ k : ℕ, ∃ z : ℤ, (den (k + 1) : ℚ) * rCoef (k + 1) = z := fun k => by
    obtain ⟨z, hz⟩ := rCoef_isInt (k + 1)
    exact ⟨den (k + 1) * z, by rw [hz]; push_cast; ring⟩
  choose p hp using hp
  choose q hq using hq
  choose r hr using hr
  have cp : ∀ k, (p k : ℝ) = (den (k + 1) : ℝ) * (pCoef (k + 1) : ℝ) := fun k => by
    have := congrArg (fun x : ℚ => (x : ℝ)) (hp k)
    push_cast at this
    exact this.symm
  have cq : ∀ k, (q k : ℝ) = (den (k + 1) : ℝ) * (qCoef (k + 1) : ℝ) := fun k => by
    have := congrArg (fun x : ℚ => (x : ℝ)) (hq k)
    push_cast at this
    exact this.symm
  have cr : ∀ k, (r k : ℝ) = (den (k + 1) : ℝ) * (rCoef (k + 1) : ℝ) := fun k => by
    have := congrArg (fun x : ℚ => (x : ℝ)) (hr k)
    push_cast at this
    exact this.symm
  have hL : ∀ k, (p k : ℝ) + q k * Real.exp 1 + r k * θ
      = (den (k + 1) : ℝ) * (Real.exp 1 * remainder (k + 1)) := fun k => by
    rw [cp, cq, cr, ← real_identity (k + 1) (by omega)]
    ring
  -- height bound for the integer coefficients
  have hB : ∀ k, |(q k : ℝ)| + |(r k : ℝ)|
      ≤ 10 * (287496 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) := fun k => by
    rw [cq, cr, abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg _), ← mul_add]
    have hH : |(qCoef (k + 1) : ℝ)| + |(rCoef (k + 1) : ℝ)|
        ≤ (9 * ((k + 1 : ℕ) : ℝ) + 1) * 108 ^ (k + 1) * ((k + 1).factorial : ℝ) := by
      have := height_bound (k + 1)
      exact_mod_cast this
    have hP := poly_le (k + 1)
    calc (den (k + 1) : ℝ) * (|(qCoef (k + 1) : ℝ)| + |(rCoef (k + 1) : ℝ)|)
        ≤ 1331 ^ (k + 1) *
            ((9 * ((k + 1 : ℕ) : ℝ) + 1) * 108 ^ (k + 1) * ((k + 1).factorial : ℝ)) :=
          mul_le_mul (den_le' _) hH (by positivity) (by positivity)
      _ ≤ 1331 ^ (k + 1) * ((10 * 2 ^ (k + 1)) * 108 ^ (k + 1) * ((k + 1).factorial : ℝ)) := by
          gcongr
      _ = 10 * (287496 : ℝ) ^ (k + 1) * ((k + 1).factorial : ℝ) := by
          rw [show (287496 : ℝ) = 1331 * 2 * 108 by norm_num, mul_pow, mul_pow]
          ring
  have hE := Real.exp_pos 1
  have hmain := LinearForms.not_mem_rat_span_of_nonvanishing_forms (Real.exp 1) θ p q r
    ?h0 ?h1 ?h2 α β
  · -- transfer to ℂ
    intro heq
    apply hmain
    apply Complex.ofReal_injective
    have hθc : ((θ : ℝ) : ℂ) = EulerMascheroni.Mixed.expEin 1 := expEin_real.symm
    rw [hθc, heq, exp_one_eq]
    push_cast
    ring
  case h0 =>
    intro k
    rw [hL]
    exact (A_bounds (k + 1)).1.ne'
  case h1 =>
    simp only [hL]
    have hlim : Tendsto (fun k : ℕ => Real.exp 1 * ((1331 : ℝ) ^ (k + 1) / (k + 1).factorial))
        atTop (𝓝 0) := by
      have := (FloorSemiring.tendsto_pow_div_factorial_atTop (1331 : ℝ)).const_mul (Real.exp 1)
      rw [mul_zero] at this
      exact (tendsto_add_atTop_iff_nat 1).mpr this
    refine squeeze_zero (fun k => (A_bounds (k + 1)).1.le) (fun k => ?_) hlim
    refine (A_bounds (k + 1)).2.trans ?_
    have hF1 : (0 : ℝ) < ((k + 1).factorial : ℝ) := by exact_mod_cast Nat.factorial_pos _
    have hF2 : ((k + 1).factorial : ℝ) ≤ ((k + 1 + 1).factorial : ℝ) := by
      exact_mod_cast Nat.factorial_le (by omega)
    have hF3 : (1 : ℝ) ≤ ((k + 1 + 1).factorial : ℝ) := by
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero _)
    rw [mul_div_assoc]
    apply mul_le_mul_of_nonneg_left _ hE.le
    apply div_le_div_of_nonneg_left (by positivity) hF1
    nlinarith
  case h2 =>
    simp only [hL]
    set K : ℝ := 10 * Real.exp 1 * (287496 + 1331) with hK
    have hlim : Tendsto
        (fun k : ℕ => K * ((1331 * 287496 : ℝ) ^ (k + 1) / (k + 1).factorial))
        atTop (𝓝 0) := by
      have := (FloorSemiring.tendsto_pow_div_factorial_atTop (1331 * 287496 : ℝ)).const_mul K
      rw [mul_zero] at this
      exact (tendsto_add_atTop_iff_nat 1).mpr this
    refine squeeze_zero (fun k => by positivity) (fun k => ?_) hlim
    rw [abs_of_pos (A_bounds (k + 1)).1, abs_of_pos (A_bounds (k + 1 + 1)).1]
    set F1 : ℝ := ((k + 1).factorial : ℝ) with hF1d
    have hF1 : 0 < F1 := by rw [hF1d]; exact_mod_cast Nat.factorial_pos _
    have hF2 : ((k + 1 + 1).factorial : ℝ) = (k + 2) * F1 := by
      rw [hF1d, Nat.factorial_succ]; push_cast; ring
    have hF3 : ((k + 1 + 1 + 1).factorial : ℝ) = (k + 3) * ((k + 2) * F1) := by
      rw [Nat.factorial_succ, Nat.cast_mul, hF2]; push_cast; ring
    have hA1 := (A_bounds (k + 1)).2
    have hA2 := (A_bounds (k + 1 + 1)).2
    have hB1 := hB (k + 1)
    have hB0 := hB k
    rw [hF2] at hA1 hB1
    rw [hF3] at hA2
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have hQ1 : (0 : ℝ) ≤ |(q (k + 1) : ℝ)| + |(r (k + 1) : ℝ)| := by positivity
    have hQ0 : (0 : ℝ) ≤ |(q k : ℝ)| + |(r k : ℝ)| := by positivity
    have T1 : (den (k + 1) : ℝ) * (Real.exp 1 * remainder (k + 1))
          * (|(q (k + 1) : ℝ)| + |(r (k + 1) : ℝ)|)
        ≤ 10 * Real.exp 1 * 287496 * ((1331 * 287496 : ℝ) ^ (k + 1) / F1) := by
      calc _ ≤ Real.exp 1 * 1331 ^ (k + 1) / ((k + 2) * F1 * ((k + 2) * F1))
            * (10 * (287496 : ℝ) ^ (k + 1 + 1) * ((k + 2) * F1)) :=
            mul_le_mul hA1 hB1 hQ1 (by positivity)
        _ = 10 * Real.exp 1 * 287496 * ((1331 * 287496 : ℝ) ^ (k + 1) / ((k + 2) * F1)) := by
            rw [mul_pow]; field_simp; ring
        _ ≤ 10 * Real.exp 1 * 287496 * ((1331 * 287496 : ℝ) ^ (k + 1) / F1) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            apply div_le_div_of_nonneg_left (by positivity) hF1
            nlinarith
    have T2 : (den (k + 1 + 1) : ℝ) * (Real.exp 1 * remainder (k + 1 + 1))
          * (|(q k : ℝ)| + |(r k : ℝ)|)
        ≤ 10 * Real.exp 1 * 1331 * ((1331 * 287496 : ℝ) ^ (k + 1) / F1) := by
      calc _ ≤ Real.exp 1 * 1331 ^ (k + 1 + 1)
              / ((k + 3) * ((k + 2) * F1) * ((k + 3) * ((k + 2) * F1)))
            * (10 * (287496 : ℝ) ^ (k + 1) * F1) :=
            mul_le_mul hA2 hB0 hQ0 (by positivity)
        _ = 10 * Real.exp 1 * 1331 * ((1331 * 287496 : ℝ) ^ (k + 1) / F1)
              * (F1 * F1 / ((k + 3) * ((k + 2) * F1) * ((k + 3) * ((k + 2) * F1)))) := by
            rw [mul_pow]; field_simp; ring
        _ ≤ 10 * Real.exp 1 * 1331 * ((1331 * 287496 : ℝ) ^ (k + 1) / F1) * 1 := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            rw [div_le_one (by positivity)]
            have h1 : F1 ≤ (k + 3) * ((k + 2) * F1) := by nlinarith
            exact mul_le_mul h1 h1 hF1.le (by positivity)
        _ = _ := mul_one _
    calc _ ≤ 10 * Real.exp 1 * 287496 * ((1331 * 287496 : ℝ) ^ (k + 1) / F1)
          + 10 * Real.exp 1 * 1331 * ((1331 * 287496 : ℝ) ^ (k + 1) / F1) := add_le_add T1 T2
      _ = K * ((1331 * 287496 : ℝ) ^ (k + 1) / F1) := by rw [hK]; ring
