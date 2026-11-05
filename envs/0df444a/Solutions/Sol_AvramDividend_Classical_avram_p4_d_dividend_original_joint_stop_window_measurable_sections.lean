-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_d_dividend_original_joint_stop_window_measurable_sections
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T22:12:26.540032+00:00
-- url     : https://prove2.me/submissions/5bb2fb16-aaa8-492a-b9d7-de7f5dfdbae2

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Joint Borel measurability of the original strict pre-ruin,
closed-horizon rightpayment window implies Borel measurability of the
actual payment set at each sample path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (σ : Ω → ℝ≥0∞) (τ : Ω → ℝ≥0)
    (hJoint : MeasurableSet {p : Ω × ℝ |
      p.2 ∈ paymentTimes (σ p.1) ∩ Iic (τ p.1 : ℝ)}) :
    ∀ ω : Ω, MeasurableSet
      (paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)) := by
  intro ω
  have hsection := hJoint.preimage
    ((measurable_const : Measurable (fun _ : ℝ => ω)).prodMk measurable_id)
  have heq : ({t : ℝ | t ∈ paymentTimes (σ ω) ∩ Iic (τ ω : ℝ)} :
      Set ℝ) = paymentTimes (σ ω) ∩ Iic (τ ω : ℝ) := by
    ext t
    rfl
  rw [← heq]
  simpa only [Set.preimage, Set.mem_setOf_eq, id_eq] using hsection
