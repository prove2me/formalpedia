-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_laplace_series_integral
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T22:27:08.91299+00:00
-- url     : https://prove2.me/submissions/5d15a9e4-adb0-40ec-873f-6f35386e089c

import Theorems.Thm_AvramDividend_Classical_nonnegative_renewal_integral_tsum_exchange
import Theorems.Thm_AvramDividend_Classical_causal_geometric_renewal_total_mass_sum
import Mathlib.Analysis.SpecificLimits.Basic
open AvramDividend.Classical MeasureTheory Set
theorem solution
    (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ ^ (n + 1)) :
    (∫ x in Ioi (0 : ℝ),
      ∑' n : ℕ, Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ / (1 - ρ) := by 
  rw [nonnegative_renewal_integral_tsum_exchange (volume.restrict (Ioi (0 : ℝ)))
    (fun n x => Real.exp (-(θ * x)) * F n x) hFi
    (fun n x => mul_nonneg (Real.exp_pos _).le (hpos n x)) ?_]
  · exact causal_geometric_renewal_total_mass_sum _ ρ hρ0 hρ1 hmass
  · simp only [hmass]
    exact (summable_geometric_of_lt_one hρ0 hρ1).mul_left ρ |>.congr fun n => by ring
