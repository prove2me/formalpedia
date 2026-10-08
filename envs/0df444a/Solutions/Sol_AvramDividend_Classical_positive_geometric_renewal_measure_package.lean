-- Prove2me | solution 1 for AvramDividend.Classical.positive_geometric_renewal_measure_package
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T17:45:51.992984+00:00
-- url     : https://prove2.me/submissions/056efc89-843b-4b3c-ba1b-11bc32fde1bf

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem solution
    (κ : Measure ℝ) [SFinite κ]
    (m : ℕ → Measure ℝ)
    (θ : ℝ) (r c : ℝ≥0∞)
    (hθ : 0 < θ)
    (hm0 : m 0 = Measure.dirac 0)
    (hmsucc : ∀ n : ℕ, m (n + 1) = Measure.conv κ (m n))
    (hsf : ∀ n : ℕ, SFinite (m n))
    (hκ : (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂κ) = r)
    (hc : 0 < c)
    (hgeom : c * (1 - c * r)⁻¹ ≠ ⊤) :
    let β : Measure ℝ := Measure.sum (fun n : ℕ => c ^ (n + 1) • m n)
    ((∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂β) = c * (1 - c * r)⁻¹) ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      0 < β {0} := by
  intro β
  set f : ℝ → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (-θ * x)) with hfdef
  have hf : Measurable f := by
    simp only [hfdef]; fun_prop
  have hmul : ∀ x y, f (x + y) = f x * f y := by
    intro x y
    simp only [hfdef]
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    ring_nf
  have hpow : ∀ n, ∫⁻ x, f x ∂(m n) = r ^ n := by
    intro n
    induction n with
    | zero => simp [hm0, lintegral_dirac, hfdef]
    | succ n ih =>
      have := hsf n
      rw [hmsucc, Measure.lintegral_conv hf]
      simp_rw [hmul]
      simp_rw [lintegral_const_mul _ hf, ih]
      rw [lintegral_mul_const _ hf, hκ, pow_succ, mul_comm]
  have hL : ∫⁻ x, f x ∂β = c * (1 - c * r)⁻¹ := by
    simp only [β]
    rw [lintegral_sum_measure]
    simp_rw [lintegral_smul_measure, hpow, smul_eq_mul]
    have : ∀ n : ℕ, c ^ (n + 1) * r ^ n = c * (c * r) ^ n := by
      intro n; rw [mul_pow, pow_succ]; ring
    simp_rw [this]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  refine ⟨hL, ?_, ?_⟩
  · intro x
    apply ne_of_lt
    calc β (Iic x) = ∫⁻ y in Iic x, 1 ∂β := (setLIntegral_one _).symm
      _ ≤ ∫⁻ y in Iic x, ENNReal.ofReal (Real.exp (θ * x)) * f y ∂β := by
          apply setLIntegral_mono (by fun_prop)
          intro y hy
          simp only [hfdef]
          rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
          exact ENNReal.one_le_ofReal.mpr (Real.one_le_exp (by
            have : y ≤ x := hy
            nlinarith))
      _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (θ * x)) * f y ∂β := setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal (Real.exp (θ * x)) * (c * (1 - c * r)⁻¹) := by
          rw [lintegral_const_mul _ hf, hL]
      _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hgeom.lt_top
  · have h1 : (c ^ (0 + 1) • m 0) {0} ≤ β {0} :=
      Measure.le_sum (fun n : ℕ => c ^ (n + 1) • m n) 0 {0}
    have h2 : (c ^ (0 + 1) • m 0) {0} = c := by simp [hm0]
    rw [h2] at h1
    exact lt_of_lt_of_le hc h1
