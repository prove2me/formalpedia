-- Prove2me | solution 1 for AvramDividend.Classical.scale_ratio_reciprocal_tendsto_of_deriv_atTop
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T11:03:26.319339+00:00
-- url     : https://prove2.me/submissions/c5058dbb-3df4-45b4-abb1-2be5430d18a1

import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.ContinuousOn
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Positivity

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set

/-- A divergent derivative forces the scale quotient to vanish at the zero boundary. -/
theorem solution
    (W : ℝ → ℝ)
    (hcont : ContinuousWithinAt W (Ici (0 : ℝ)) 0)
    (hderiv : Tendsto
      (fun n : ℕ => deriv W (1 / ((n : ℝ) + 1)))
      atTop atTop) :
    Tendsto
      (fun n : ℕ => W (1 / ((n : ℝ) + 1)) /
        deriv W (1 / ((n : ℝ) + 1)))
      atTop (nhds (0 : ℝ)) := by
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhds (0 : ℝ)) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hrwithin : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1))
      atTop (nhdsWithin (0 : ℝ) (Ici 0)) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hr, ?_⟩
    exact Filter.Eventually.of_forall (fun n : ℕ => by
      exact le_of_lt (by positivity : (0 : ℝ) < 1 / ((n : ℝ) + 1)))
  have hW : Tendsto (fun n : ℕ => W (1 / ((n : ℝ) + 1)))
      atTop (nhds (W 0)) := hcont.tendsto.comp hrwithin
  have hInv : Tendsto (fun n : ℕ =>
      (deriv W (1 / ((n : ℝ) + 1)))⁻¹)
      atTop (nhds (0 : ℝ)) := hderiv.inv_tendsto_atTop
  simpa only [div_eq_mul_inv, mul_zero] using hW.mul hInv
