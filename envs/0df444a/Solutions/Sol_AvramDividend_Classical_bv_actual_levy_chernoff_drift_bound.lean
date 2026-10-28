-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_chernoff_drift_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:43:54.743376+00:00
-- url     : https://prove2.me/submissions/5206da30-6f65-473d-add2-15084139b57d

import Theorems.Thm_AvramDividend_Classical_bv_laplace_exponent_le_drift_mul
import Mathlib.Probability.Moments.Basic
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

/-- A Chernoff bound above the deterministic drift line of the actual BV Levy process. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (θ ε : ℝ) (hθ : 1 ≤ θ) :
    P.real {ω : Ω | (t : ℝ) * X.drift + ε ≤ X.X t ω} ≤
      Real.exp (-θ * ε) := by
  letI : IsProbabilityMeasure P := X.isProbability
  have hθ0 : 0 ≤ θ := le_trans (by norm_num) hθ
  have hlap := (X.laplace t θ hθ0).2
  change (∫ ω, Real.exp (θ * X.X t ω) ∂P) =
      Real.exp ((t : ℝ) * X.ψ θ) at hlap
  have hch := ProbabilityTheory.measure_ge_le_exp_mul_mgf
    (X := X.X t) (μ := P) ((t : ℝ) * X.drift + ε) hθ0
    (X.laplace t θ hθ0).1
  change P.real {ω : Ω | (t : ℝ) * X.drift + ε ≤ X.X t ω} ≤
    Real.exp (-θ * ((t : ℝ) * X.drift + ε)) *
      (∫ ω, Real.exp (θ * X.X t ω) ∂P) at hch
  rw [hlap] at hch
  have hpsi := bv_laplace_exponent_le_drift_mul X hBV θ hθ
  have ht0 : 0 ≤ (t : ℝ) := t.property
  have htpsi : (t : ℝ) * X.ψ θ ≤ (t : ℝ) * (X.drift * θ) :=
    mul_le_mul_of_nonneg_left hpsi ht0
  calc
    P.real {ω : Ω | (t : ℝ) * X.drift + ε ≤ X.X t ω} ≤
      Real.exp (-θ * ((t : ℝ) * X.drift + ε)) *
        Real.exp ((t : ℝ) * X.ψ θ) := hch
    _ = Real.exp (-θ * ((t : ℝ) * X.drift + ε) +
        (t : ℝ) * X.ψ θ) := by rw [Real.exp_add]
    _ ≤ Real.exp (-θ * ε) := by
      apply Real.exp_le_exp.mpr
      nlinarith [htpsi]
