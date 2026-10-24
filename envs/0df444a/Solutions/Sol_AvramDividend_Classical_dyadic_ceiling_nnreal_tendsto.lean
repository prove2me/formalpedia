-- Prove2me | solution 1 for AvramDividend.Classical.dyadic_ceiling_nnreal_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T21:00:43.834382+00:00
-- url     : https://prove2.me/submissions/dd345a35-fe35-4fec-aeb3-350718f751a3

import Mathlib.Topology.Instances.NNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_dyadic_ceiling_rounding_tendsto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Topology
open scoped NNReal ENNReal

/-- Dyadic upper rounding converges in nonnegative-real time itself. -/
theorem solution
    (t : ℝ≥0) :
    Tendsto
      (fun n : ℕ =>
        (Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) / (2 : ℝ≥0) ^ n)
      atTop (𝓝 t) := by
  have hreal : Tendsto
      (fun n : ℕ =>
        (((Nat.ceil ((t : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
          (2 : ℝ≥0) ^ n) : ℝ))
      atTop (𝓝 (t : ℝ)) := by
    simpa only [NNReal.coe_div, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_ofNat]
      using (dyadic_ceiling_rounding_tendsto t)
  first
  | exact NNReal.tendsto_coe.mpr hreal
  | exact NNReal.tendsto_coe.mp hreal