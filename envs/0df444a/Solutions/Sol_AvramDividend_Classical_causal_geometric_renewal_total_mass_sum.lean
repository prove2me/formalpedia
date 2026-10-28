-- Prove2me | solution 1 for AvramDividend.Classical.causal_geometric_renewal_total_mass_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T10:38:28.728988+00:00
-- url     : https://prove2.me/submissions/9de007ea-4efb-45aa-9a9d-df12e21d2db8

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Total renewal mass is the geometric resolvent rho / (1-rho). -/
theorem solution
    (F : ℕ → ℝ → ℝ) (ρ : ℝ)
    (hρnonneg : 0 ≤ ρ) (hρlt : ρ < 1)
    (hmass : ∀ n : ℕ,
      (∫ x in Ioi (0 : ℝ), F n x ∂volume) = ρ ^ (n + 1)) :
    (∑' n : ℕ, ∫ x in Ioi (0 : ℝ), F n x ∂volume) =
      ρ / (1 - ρ) := by
  simp_rw [hmass, pow_succ]
  rw [tsum_mul_right]
  rw [tsum_geometric_of_lt_one hρnonneg hρlt]
  simp [div_eq_mul_inv, mul_comm]
