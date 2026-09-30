-- Prove2me | solution 3 for EthierKurtz.kmt_strong_approximation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Eyal1990
-- created : 2026-09-29T20:27:02.202853+00:00
-- url     : https://prove2.me/submissions/20b4a27a-b7f2-43dc-ba75-630bc5e1f176
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_EthierKurtz_kmt_discrete_coupling
import Theorems.Thm_EthierKurtz_kmt_discrete_to_brownian
import Theorems.Thm_EthierKurtz_kmt_affine_transfer

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators
open EthierKurtz

theorem solution
    (μ : ProbabilityMeasure Real)
    (hexp : Exists fun a0 : Real => 0 < a0∧∀ a : Real, abs a <= a0 ->
      Integrable (fun x : Real => Real.exp (a * x)) (μ : Measure Real)) :
      ∃ Q : ProbabilityMeasure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}),
      iIndepFun (fun (i : ℕ) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      (∀ i : ℕ, HasLaw (fun (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.1 i) (μ : Measure ℝ) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}))) ∧
      IsBrownianReal (fun t (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) => z.2.val t) (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) ∧
      ∃ C K lam : ℝ, 0 < C ∧ 0 < K ∧ 0 < lam ∧
        let m := ∫ x : ℝ, x ∂(μ : Measure ℝ)
        let σ := Real.sqrt (variance (fun x : ℝ => x) (μ : Measure ℝ))
        let W := fun (t : ℝ≥0) (z : (ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b}) =>
          m * (t : ℝ) + σ * z.2.val t
        ∀ n : ℕ, 1 ≤ n → ∀ x : ℝ, 0 < x →
          (Q : Measure ((ℕ → ℝ) × {b : ℝ≥0 → ℝ // Continuous b})) {z | ∃ k : ℕ, 1 ≤ k ∧ k ≤ n ∧
            C * Real.log (n : ℝ) + x <
              |(∑ i ∈ Finset.range k, z.1 i) - W (k : ℝ≥0) z|} <
            ENNReal.ofReal (K * Real.exp (-lam * x)) := by
  apply EthierKurtz.kmt_affine_transfer ?_ μ hexp
  intro ν hν hmean hvariance
  exact EthierKurtz.kmt_discrete_to_brownian ν hmean hvariance
    (EthierKurtz.kmt_discrete_coupling ν hν hmean hvariance)
