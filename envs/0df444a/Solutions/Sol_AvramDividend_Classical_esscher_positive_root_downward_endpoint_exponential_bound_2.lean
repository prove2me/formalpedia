-- Prove2me | solution 2 for AvramDividend.Classical.esscher_positive_root_downward_endpoint_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T23:15:10.342006+00:00
-- url     : https://prove2.me/submissions/ec9dfdc1-5b63-402b-a13a-ab287dd936e9

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Theorems.Thm_AvramDividend_Classical_chat04_esscher_finite_downward_endpoint_chernoff_bound
import Theorems.Thm_AvramDividend_Classical_levy_psi_positive_secant_monotone
open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

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
  have h1 := chat04_esscher_finite_downward_endpoint_chernoff_bound X t φ (φ / 2) b hφ.le
    (by linarith) (by linarith)
  have h2 := levy_psi_positive_secant_monotone X (φ / 2) φ (by linarith) (by linarith)
  rw [hroot] at h2
  have h3 : X.ψ (φ / 2) ≤ q / 2 := by
    rw [div_le_div_iff₀ (by linarith) hφ] at h2
    nlinarith
  have e : φ - φ / 2 = φ / 2 := by ring
  rw [e] at h1
  refine h1.trans (ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_))
  have : (0:ℝ) ≤ t := t.2
  rw [hroot]
  nlinarith
