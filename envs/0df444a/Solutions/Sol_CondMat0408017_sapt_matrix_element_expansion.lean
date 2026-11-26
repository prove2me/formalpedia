-- Prove2me | solution 1 for CondMat0408017.sapt_matrix_element_expansion
-- status  : ACCEPTED   (prove)
-- author  : @fl-39
-- created : 2026-11-26T17:29:01.108203+00:00
-- url     : https://prove2.me/submissions/b000657f-bb72-48b4-bb06-2f72d1483ea4

import Mathlib
import Definitions.Def_CondMat0408017_Basic

open MeasureTheory Filter Topology Complex CondMat0408017

theorem solution (ζ : ℝ → ℝ) (hζ : Continuous ζ) (L : ℝ) (hL : 0 < L) :
    (∀ (γ : ℂ) (Q : ℝ),
      HasSum (fun n : ℕ => (-I * γ) ^ n / (n.factorial : ℂ) * zetaPowFT ζ L n Q)
        (zetaIntL ζ L γ Q)) ∧
    (∀ sgn : ℂ, (sgn = 1 ∨ sgn = -1) → ∀ (p q : ℝ) (a a0 : ℂ), a - sgn * a0 ≠ 0 →
      HasSum (fun n : ℕ => rreNpCoeff sgn n p q a a0 / (n.factorial : ℂ) * zetaPowFT ζ L n (p - q))
          (rreNp sgn p q a a0 * zetaIntL ζ L (a - sgn * a0) (p - q)) ∧
        HasSum (fun n : ℕ => rreNsCoeff sgn n a a0 / (n.factorial : ℂ) * zetaPowFT ζ L n (p - q))
          (rreNs sgn a a0 * zetaIntL ζ L (a - sgn * a0) (p - q))) ∧
    (∀ (sgn eps : ℂ) (wv p : ℝ) (a a0 : ℂ), (sgn = 1 ∨ sgn = -1) →
      a ^ 2 = eps * wv ^ 2 - p ^ 2 → a0 ^ 2 = wv ^ 2 - p ^ 2 → eps ≠ 1 → wv ≠ 0 →
      rreNpCoeff sgn 0 p p a a0 = (eps * a0 + sgn * a) / (eps - 1) ∧
        rreNsCoeff sgn 0 a a0 = (a0 + sgn * a) / ((wv : ℂ) ^ 2 * (eps - 1))) := by
  have hpart1 : ∀ (γ : ℂ) (Q : ℝ),
      HasSum (fun n : ℕ => (-I * γ) ^ n / (n.factorial : ℂ) * zetaPowFT ζ L n Q)
        (zetaIntL ζ L γ Q) := by
    intro γ Q
    have hle : -(L / 2) ≤ L / 2 := by linarith
    obtain ⟨M, hM⟩ := (isCompact_Icc (a := -(L / 2)) (b := L / 2)).exists_bound_of_continuousOn
      hζ.continuousOn
    set C : ℝ := max M 0
    have hC0 : 0 ≤ C := le_max_right M 0
    have hζ_le : ∀ x ∈ Set.Icc (-(L / 2)) (L / 2), ‖(ζ x : ℂ)‖ ≤ C := by
      intro x hx
      rw [Complex.norm_real]
      exact (hM x hx).trans (le_max_left M 0)
    let μ : Measure ℝ := volume.restrict (Set.Ioc (-(L / 2)) (L / 2))
    let F : ℕ → ℝ → ℂ := fun n x =>
      (-I * γ) ^ n / (n.factorial : ℂ) * ((ζ x : ℂ) ^ n * cexp (-I * Q * x))
    let bound : ℕ → ℝ := fun n => (‖γ‖ * C) ^ n / (n.factorial : ℝ)
    have hsum_bound : Summable (fun n => ∫ _x, bound n ∂μ) := by
      have hconst : (fun n => ∫ _x, bound n ∂μ) = fun n => L * bound n := by
        ext n
        simp only [μ]
        rw [setIntegral_const, smul_eq_mul, Real.volume_real_Ioc_of_le hle]
        ring
      rw [hconst]
      exact (Real.summable_pow_div_factorial (‖γ‖ * C)).mul_left L
    have hF_int : ∀ n, Integrable (F n) μ := by
      intro n
      have hcont : Continuous (F n) := by
        unfold F
        fun_prop
      exact hcont.integrableOn_Ioc
    have hF_norm : ∀ n, ∀ᵐ x ∂μ, ‖F n x‖ ≤ bound n := by
      intro n
      refine (ae_restrict_mem measurableSet_Ioc).mono (fun x hx => ?_)
      have hx' : x ∈ Set.Icc (-(L / 2)) (L / 2) := Set.Ioc_subset_Icc_self hx
      have hre : (-I * (Q : ℂ) * (x : ℂ)).re = 0 := by simp
      simp only [F, bound, norm_mul, norm_div, norm_pow, norm_neg, Complex.norm_I, one_mul,
        Complex.norm_natCast, Complex.norm_exp, hre, Real.exp_zero, mul_one]
      rw [mul_pow, div_mul_eq_mul_div]
      gcongr
      exact hζ_le x hx'
    have hsum_norm : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
      refine Summable.of_nonneg_of_le (fun n => integral_nonneg (fun _ => norm_nonneg _))
        (fun n => ?_) hsum_bound
      have hb_int : Integrable (fun _x => bound n) μ := by
        simp only [μ]
        exact integrableOn_const (by simp)
      exact integral_mono_ae (hF_int n).norm hb_int (hF_norm n)
    have hF_hasSum : ∀ x, HasSum (fun n => F n x) (cexp (-I * γ * ζ x - I * Q * x)) := by
      intro x
      have hexp : HasSum (fun n : ℕ => (-I * γ * (ζ x : ℂ)) ^ n / (n.factorial : ℂ))
          (cexp (-I * γ * (ζ x : ℂ))) := by
        rw [Complex.exp_eq_exp_ℂ]
        simpa [div_eq_inv_mul] using NormedSpace.expSeries_div_hasSum_exp (-I * γ * (ζ x : ℂ))
      have hmul := hexp.mul_right (cexp (-I * (Q : ℂ) * (x : ℂ)))
      have heq_rhs : cexp (-I * γ * (ζ x : ℂ)) * cexp (-I * (Q : ℂ) * (x : ℂ)) =
          cexp (-I * γ * (ζ x : ℂ) - I * (Q : ℂ) * (x : ℂ)) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      rw [heq_rhs] at hmul
      refine hmul.congr_fun (fun n => ?_)
      simp only [F, mul_pow]
      ring
    have hmain := MeasureTheory.hasSum_integral_of_summable_integral_norm hF_int hsum_norm
    have htsum : (fun x => ∑' n, F n x) = fun x => cexp (-I * γ * ζ x - I * Q * x) := by
      ext x
      exact (hF_hasSum x).tsum_eq
    rw [htsum] at hmain
    simp only [zetaIntL, zetaPowFT, intervalIntegral.integral_of_le hle]
    refine hmain.congr_fun (fun n => ?_)
    simp only [F, μ, integral_const_mul]
  refine ⟨hpart1, ?_, ?_⟩
  · intro sgn hsgn p q a a0 hne
    constructor
    · refine ((hpart1 (a - sgn * a0) (p - q)).mul_left (rreNp sgn p q a a0)).congr_fun (fun n => ?_)
      cases n with
      | zero =>
        simp [rreNpCoeff]
      | succ m =>
        simp only [rreNpCoeff, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, rreNp]
        have hpow : (-I * (a - sgn * a0)) ^ (m + 1) =
            (-I) ^ (m + 1) * (a - sgn * a0) ^ m * (a - sgn * a0) := by
          rw [mul_pow, pow_succ]
          ring
        rw [hpow]
        rcases hsgn with rfl | rfl <;>
          simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hne ⊢ <;>
          field_simp [hne] <;>
          ring
    · refine ((hpart1 (a - sgn * a0) (p - q)).mul_left (rreNs sgn a a0)).congr_fun (fun n => ?_)
      cases n with
      | zero =>
        simp [rreNsCoeff]
      | succ m =>
        simp only [rreNsCoeff, Nat.succ_ne_zero, ↓reduceIte, Nat.add_sub_cancel, rreNs]
        have hpow : (-I * (a - sgn * a0)) ^ (m + 1) =
            (-I) ^ (m + 1) * (a - sgn * a0) ^ m * (a - sgn * a0) := by
          rw [mul_pow, pow_succ]
          ring
        rw [hpow]
        field_simp [hne]
  · intro sgn eps wv p a a0 hsgn ha ha0 heps hwv
    have hsgn2 : sgn ^ 2 = 1 := by rcases hsgn with rfl | rfl <;> norm_num
    have heps_ne : eps - 1 ≠ 0 := sub_ne_zero.mpr heps
    have hwv_ne : (wv : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hwv
    have hdiff_ne : a - sgn * a0 ≠ 0 := by
      intro h0
      have h1 : a = sgn * a0 := sub_eq_zero.mp h0
      have h2 : a ^ 2 = a0 ^ 2 := by
        rw [h1, mul_pow, hsgn2, one_mul]
      have h3 : (eps - 1) * (wv : ℂ) ^ 2 = 0 := by
        linear_combination h2 - ha + ha0
      rcases mul_eq_zero.mp h3 with h | h
      · exact heps_ne h
      · exact pow_ne_zero 2 hwv_ne h
    constructor
    · simp only [rreNpCoeff, ↓reduceIte, rreNp]
      rcases hsgn with rfl | rfl <;>
        simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hdiff_ne ⊢ <;>
        field_simp [hdiff_ne, heps_ne]
      · linear_combination -ha + eps * ha0
      · linear_combination ha - eps * ha0
    · simp only [rreNsCoeff, ↓reduceIte, rreNs]
      rcases hsgn with rfl | rfl <;>
        simp only [one_mul, neg_one_mul, sub_neg_eq_add] at hdiff_ne ⊢ <;>
        field_simp [hdiff_ne, heps_ne, hwv_ne]
      · linear_combination -ha + ha0
      · linear_combination ha - ha0
