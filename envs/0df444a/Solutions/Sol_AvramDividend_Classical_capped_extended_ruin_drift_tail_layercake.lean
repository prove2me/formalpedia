-- Prove2me | solution 1 for AvramDividend.Classical.capped_extended_ruin_drift_tail_layercake
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:46:59.848853+00:00
-- url     : https://prove2.me/submissions/e54c9915-88bd-48d4-a0e5-e2805c89c8cf

import Theorems.Thm_AvramDividend_Classical_stopped_discounted_drift_tail_layercake
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Data.NNReal.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Apply strict-survival layer cake to a finite cap of an extended-real ruin clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω)
    (τ : Ω → ℝ≥0∞) (hτ : Measurable τ)
    (T : ℝ≥0) (d q : ℝ) (hd : 0 ≤ d) :
    (∫⁻ ω, ENNReal.ofReal
        (∫ t in (0 : ℝ)..(min (τ ω) (T : ℝ≥0∞)).toReal,
          d * Real.exp (-(q * t))) ∂P) =
      ∫⁻ t in Ioi (0 : ℝ),
        P {ω : Ω | t < (min (τ ω) (T : ℝ≥0∞)).toReal} *
          ENNReal.ofReal (d * Real.exp (-(q * t))) := by
  let S : Ω → ℝ := fun ω => (min (τ ω) (T : ℝ≥0∞)).toReal
  have hS : Measurable S :=
    ENNReal.measurable_toReal.comp (hτ.min measurable_const)
  have hpos : ∀ᵐ ω ∂P, 0 ≤ S ω :=
    Filter.Eventually.of_forall fun ω => ENNReal.toReal_nonneg
  exact stopped_discounted_drift_tail_layercake P S hS hpos d q hd
