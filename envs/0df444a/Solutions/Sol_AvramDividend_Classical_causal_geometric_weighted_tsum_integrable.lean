-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_weighted_tsum_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:34:34.914283+00:00
-- url     : https://prove2.me/submissions/b31649e5-1fb3-402b-a768-8d26bfd562c7

import Theorems.Thm_AvramDividend_Classical_nonnegative_integrable_tsum_of_summable_integrals
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set

/-- A geometrically bounded nonnegative renewal series is weighted-integrable. -/
theorem solution
    (F : ℕ → ℝ → ℝ) (θ ρ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hFi : ∀ n : ℕ, IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume)
    (hpos : ∀ n : ℕ, ∀ x : ℝ, 0 ≤ F n x)
    (hpoint : ∀ x : ℝ,
      Summable (fun n : ℕ => Real.exp (-(θ * x)) * F n x))
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) * F n x ∂volume) =
        ρ ^ (n + 1)) :
    IntegrableOn
      (fun x : ℝ => ∑' n : ℕ, Real.exp (-(θ * x)) * F n x)
      (Ioi (0 : ℝ)) volume := by
  let G : ℕ → ℝ → ℝ := fun n x =>
    Real.exp (-(θ * x)) * F n x
  have hGi (n : ℕ) :
      Integrable (G n) (volume.restrict (Ioi (0 : ℝ))) := hFi n
  have hGp (n : ℕ) (x : ℝ) : 0 ≤ G n x :=
    mul_nonneg (le_of_lt (Real.exp_pos _)) (hpos n x)
  have hGs (x : ℝ) : Summable (fun n : ℕ => G n x) := hpoint x
  have hGmass (n : ℕ) :
      (∫ x, G n x ∂(volume.restrict (Ioi (0 : ℝ)))) =
        ρ ^ (n + 1) := hmass n
  have hGtotal : Summable
      (fun n : ℕ => ∫ x, G n x ∂(volume.restrict (Ioi (0 : ℝ)))) := by
    simp_rw [hGmass]
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_lt_one hρ0 hρ1).mul_left ρ
  exact nonnegative_integrable_tsum_of_summable_integrals
    (volume.restrict (Ioi (0 : ℝ))) G hGi hGp hGs hGtotal
