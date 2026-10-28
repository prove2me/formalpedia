-- Prove2me | solution 1 for AvramDividend.Classical.bv_actual_levy_drift_upper_zero_probability
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T08:51:17.293984+00:00
-- url     : https://prove2.me/submissions/d08cd10d-f392-4e96-bd0f-f80002502235

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_chernoff_drift_bound
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Measure.Real

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

/-- The actual bounded-variation Levy process cannot exceed its drift line at positive fixed times. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    P.real {ω : Ω | (t : ℝ) * X.drift + ε ≤ X.X t ω} = 0 := by
  have hcast : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have hn : Tendsto (fun n : ℕ => (n : ℝ) + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop 1 hcast
  have htop : Tendsto (fun n : ℕ => ((n : ℝ) + 1) * ε) atTop atTop :=
    hn.atTop_mul_pos hε tendsto_const_nhds
  have hlim : Tendsto
      (fun n : ℕ => Real.exp (-(((n : ℝ) + 1) * ε)))
      atTop (nhds (0 : ℝ)) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp htop
  have hle :
      P.real {ω : Ω | (t : ℝ) * X.drift + ε ≤ X.X t ω} ≤ 0 := by
    apply ge_of_tendsto' hlim
    intro n
    have hθ : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have := Nat.cast_nonneg (α := ℝ) n
      linarith
    simpa only [neg_mul] using
      (bv_actual_levy_chernoff_drift_bound X hBV t
        ((n : ℝ) + 1) ε hθ)
  exact le_antisymm hle measureReal_nonneg
