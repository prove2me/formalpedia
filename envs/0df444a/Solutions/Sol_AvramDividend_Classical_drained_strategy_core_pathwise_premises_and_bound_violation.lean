-- Prove2me | solution 1 for AvramDividend.Classical.drained_strategy_core_pathwise_premises_and_bound_violation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T21:43:02.703254+00:00
-- url     : https://prove2.me/submissions/37dbbea0-0cdb-41a5-b215-1bc8e7f6884e

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_admissible_infinite_cap
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_ruinTime_zero
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_affine_jump_control
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_no_nonpositive_expected_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 < x)
    (w : ℝ → ℝ) (hw_affine : ∀ y, 0 ≤ y → w y = y - 1)
    (hwx : w x ≤ 0) (q T : ℝ) (hT : 0 ≤ T) :
    let D : ℝ≥0 → Ω → ℝ :=
      fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)
    IsAdmissibleLe X x ⊤ D ∧
    (∀ ω (t : ℝ≥0), 0 < t →
      (t : ℝ≥0∞) < ruinTime X x D ω →
      0 ≤ w (riskProcess X x D t ω)) ∧
    (∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω))) ∧
    ¬ ((∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω) ∂P) ≤ ENNReal.ofReal (w x)) := by
  dsimp only
  refine ⟨drained_zero_barrier_admissible_infinite_cap X x hx.le, ?_, ?_, ?_⟩
  · intro ω t ht hbefore
    have hzero :=
      barrierStrategy_plus_linear_drain_ruinTime_zero X x hx.le ω
    simp [hzero] at hbefore
  · exact drained_zero_barrier_affine_jump_control X x hx.le w hw_affine
  · exact drained_zero_barrier_no_nonpositive_expected_bound X x hx w hwx q T hT
