-- Prove2me | solution 1 for AvramDividend.Classical.barrierSupValue_le_expected_qDiscount_record_sum
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T22:57:43.589644+00:00
-- url     : https://prove2.me/submissions/58b004cf-4f23-48d9-9901-c167a1a448a3

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_stopped_partition_record_upper
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a q : ℝ) (hq : 0 ≤ q)
    (u : ℕ → ℝ) (hu : Monotone u)
    (hcofinal : ∀ x : ℝ, ∃ n : ℕ, x ≤ u n)
    (hstart : u 0 < 0) :
    barrierSupValue X a q ≤
      (∫⁻ ω, (∑' i : ℕ,
        ENNReal.ofReal (Real.exp (-(q * u i))) *
        ENNReal.ofReal
          (runningSup X (u (i + 1)).toNNReal ω -
           runningSup X (u i).toNNReal ω)) ∂P) := by
  unfold barrierSupValue
  apply lintegral_mono
  intro ω
  exact runningSup_qDiscount_stopped_partition_record_upper
    X ω (barrierRuinTime X a ω) q hq u hu hcofinal hstart
