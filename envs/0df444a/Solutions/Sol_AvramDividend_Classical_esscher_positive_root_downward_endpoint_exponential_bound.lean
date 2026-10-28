-- Prove2me | solution 1 for AvramDividend.Classical.esscher_positive_root_downward_endpoint_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:14:27.412385+00:00
-- url     : https://prove2.me/submissions/1305df59-7b67-4d03-ae4f-513688938dc6

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_downward_endpoint_chernoff_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q φ b : ℝ) (hq : 0 < q) (hφ : 0 < φ)
    (hroot : X.ψ φ = q) (t : ℝ≥0) :
    ENNReal.ofReal (Real.exp ((φ / 2) * b)) *
      (P.withDensity (fun ω : Ω => ENNReal.ofReal
        (Real.exp (φ * X.X t ω - (t : ℝ) * X.ψ φ))))
        {ω : Ω | X.X t ω ≤ -b} ≤
      ENNReal.ofReal (Real.exp (-(t : ℝ) * q / 2)) := by
  have hhalf : 0 < φ / 2 := by linarith
  have hsec : X.ψ (φ / 2) / (φ / 2) ≤ X.ψ φ / φ :=
    levy_psi_positive_secant_monotone X (φ / 2) φ hhalf (by linarith)
  have hmul : X.ψ (φ / 2) * φ ≤ X.ψ φ * (φ / 2) :=
    (div_le_div_iff₀ hhalf hφ).mp hsec
  have hpsi : X.ψ (φ - φ / 2) - X.ψ φ ≤ -q / 2 := by
    have heq : φ - φ / 2 = φ / 2 := by ring
    rw [heq, hroot]
    nlinarith [hmul]
  have ht : 0 ≤ (t : ℝ) := by positivity
  have harg : (t : ℝ) * (X.ψ (φ - φ / 2) - X.ψ φ) ≤
      -(t : ℝ) * q / 2 := by
    calc
      _ ≤ (t : ℝ) * (-q / 2) := mul_le_mul_of_nonneg_left hpsi ht
      _ = -(t : ℝ) * q / 2 := by ring
  have hch := chat04_esscher_finite_downward_endpoint_chernoff_bound
    X t φ (φ / 2) b (le_of_lt hφ) hhalf (by linarith)
  exact hch.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr harg))
