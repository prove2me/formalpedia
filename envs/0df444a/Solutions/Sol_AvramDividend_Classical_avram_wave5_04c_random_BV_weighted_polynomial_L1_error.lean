-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_random_BV_weighted_polynomial_L1_error
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:37:39.742624+00:00
-- url     : https://prove2.me/submissions/2357a87b-bf65-4f45-b329-348f2daabc80

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open MeasureTheory Set
open scoped NNReal ENNReal

/-! Genuine BV first-moment random residual domination for a fixed
exponential polynomial approximating a continuous C1 payoff loss. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (R : Ω → ℝ) (hRm : Measurable R)
    (hRnn : ∀ᵐ ω ∂P, 0 ≤ R ω) (hRi : Integrable R P)
    (M ε K : ℝ) (hε : 0 ≤ ε) (hK : 0 ≤ K)
    (hTail : Integrable (fun ω => if M < R ω then R ω else 0) P)
    (f : ℝ → ℝ) (hf : Continuous f) (Q : Polynomial ℝ)
    (hPoint : ∀ r : ℝ, 0 ≤ r →
      |Polynomial.eval (Real.exp (-r)) Q - f r| ≤
      ε * (1 - Real.exp (-r)) +
        (if M < r then K * r else 0)) :
    |∫ ω, f (R ω) - Polynomial.eval (Real.exp (-R ω)) Q ∂P| ≤
      ε * (∫ ω, R ω ∂P) +
        K * (∫ ω, if M < R ω then R ω else 0 ∂P) := by
  let E : Ω → ℝ := fun ω => f (R ω) -
    Polynomial.eval (Real.exp (-R ω)) Q
  let T : Ω → ℝ := fun ω => if M < R ω then R ω else 0
  have hQcont : Continuous (fun r : ℝ =>
      Polynomial.eval (Real.exp (-r)) Q) := by
    fun_prop
  have hEm : AEStronglyMeasurable E P := by
    exact ((hf.measurable.comp hRm).sub
      (hQcont.measurable.comp hRm)).aestronglyMeasurable
  have hTI : Integrable T P := hTail
  have hDI : Integrable (fun ω => ε * R ω + K * T ω) P :=
    (hRi.const_mul ε).add (hTI.const_mul K)
  have hD : ∀ᵐ ω ∂P, |E ω| ≤ ε * R ω + K * T ω := by
    filter_upwards [hRnn] with ω hr
    have hs := hPoint (R ω) hr
    have he : 1 - Real.exp (-R ω) ≤ R ω := by
      have hh := Real.add_one_le_exp (-R ω)
      linarith
    have htail : (if M < R ω then K * R ω else 0) = K * T ω := by
      by_cases hm : M < R ω <;> simp [T, hm]
    calc
      |E ω| = |Polynomial.eval (Real.exp (-R ω)) Q - f (R ω)| :=
        abs_sub_comm _ _
      _ ≤ ε * (1 - Real.exp (-R ω)) +
        (if M < R ω then K * R ω else 0) := hs
      _ ≤ ε * R ω + K * T ω := by
        rw [htail]
        exact add_le_add (mul_le_mul_of_nonneg_left he hε) le_rfl
  have hEI : Integrable E P := by
    apply hDI.mono' hEm
    filter_upwards [hD] with ω hω
    simpa only [Real.norm_eq_abs] using hω
  have hmono : (∫ ω, |E ω| ∂P) ≤
      ∫ ω, ε * R ω + K * T ω ∂P :=
    integral_mono_ae hEI.abs hDI hD
  calc
    |∫ ω, f (R ω) - Polynomial.eval (Real.exp (-R ω)) Q ∂P| =
      |∫ ω, E ω ∂P| := rfl
    _ ≤ ∫ ω, |E ω| ∂P := abs_integral_le_integral_abs
    _ ≤ ∫ ω, ε * R ω + K * T ω ∂P := hmono
    _ = ε * (∫ ω, R ω ∂P) +
      K * (∫ ω, if M < R ω then R ω else 0 ∂P) := by
        rw [integral_add (hRi.const_mul ε) (hTI.const_mul K)]
        simp only [integral_const_mul, T]
