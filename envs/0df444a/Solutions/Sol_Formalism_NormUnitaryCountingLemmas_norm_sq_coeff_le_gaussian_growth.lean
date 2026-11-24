-- Prove2me | solution 1 for Formalism.NormUnitaryCountingLemmas.norm_sq_coeff_le_gaussian_growth
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:43:08.662844+00:00
-- url     : https://prove2.me/submissions/84731847-f414-4731-839f-c12a851cca9a

import Definitions.Def_Formalism_NormUnitaryBounds_Statement
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_IntegralExpInt
import Definitions.Def_Formalism_NormUnitaryBounds_DetPolynomialWeights_GaussianCoefficientFactorialBound
import Theorems.Thm_Formalism_NormUnitaryCountingLemmas_ExponentialIntegralMeasures_cauchy_torus


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Complex
noncomputable section
open Formalism Formalism.NormUnitaryCountingLemmas
open ExponentialIntegralMeasures
namespace Formalism.NormUnitaryCountingLemmas
theorem _root_.solution (G : ℕ) (Θ : (Fin G → ℂ) → ℂ) (c : (Fin G → ℕ) → ℂ) (S : ℝ)
    (hΘ : ∀ z : Fin G → ℂ, HasSum (fun e : Fin G → ℕ => c e * ∏ i, z i ^ e i) (Θ z))
    (hS : ∀ z : Fin G → ℂ, ‖Θ z‖ ≤ S * Real.exp ((∑ i, ‖z i‖ ^ 2) / 2))
    (e : Fin G → ℕ) :
    ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i ≤ S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by
  set r : Fin G → ℝ := fun i => Real.sqrt (e i) with hr
  have hB : ∀ θ : Fin G → ℝ, ‖Θ (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))‖ ≤
      S * Real.exp ((∑ i, (e i : ℝ)) / 2) := by
    intro θ
    have h := hS (fun i => (r i : ℂ) * Complex.exp ((θ i : ℂ) * I))
    have hz : ∀ i, ‖(r i : ℂ) * Complex.exp ((θ i : ℂ) * I)‖ ^ 2 = (e i : ℝ) := by
      intro i
      rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
        sq_abs, hr, Real.sq_sqrt (Nat.cast_nonneg _)]
    simp only [hz] at h
    exact h
  have h1 := cauchy_torus G Θ c hΘ r _ hB e
  have hr' : ∀ i, |r i| = Real.sqrt (e i) := fun i => abs_of_nonneg (Real.sqrt_nonneg _)
  simp only [hr'] at h1
  have h0 : 0 ≤ ‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i := by positivity
  have h2 := pow_le_pow_left₀ h0 h1 2
  have hl : (‖c e‖ * ∏ i, Real.sqrt (e i) ^ e i) ^ 2 = ‖c e‖ ^ 2 * ∏ i, ((e i : ℝ)) ^ e i := by
    rw [mul_pow, ← Finset.prod_pow]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, mul_comm, pow_mul, Real.sq_sqrt (Nat.cast_nonneg _)]
  have hrr : (S * Real.exp ((∑ i, (e i : ℝ)) / 2)) ^ 2 = S ^ 2 * Real.exp (∑ i, (e i : ℝ)) := by
    rw [mul_pow, sq (Real.exp _), ← Real.exp_add]
    congr 2; ring
  rw [hl, hrr] at h2
  exact h2
end Formalism.NormUnitaryCountingLemmas
