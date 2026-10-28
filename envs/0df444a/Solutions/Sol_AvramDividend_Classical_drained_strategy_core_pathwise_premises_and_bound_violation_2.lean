-- Prove2me | solution 2 for AvramDividend.Classical.drained_strategy_core_pathwise_premises_and_bound_violation
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-26T21:45:01.13154+00:00
-- url     : https://prove2.me/submissions/b2819060-161b-464b-ab62-12e53f46cff9

import Mathlib.Data.ENNReal.Real
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_admissible_infinite_cap
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_ruinTime_zero
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_affine_jump_control
import Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_no_nonpositive_expected_bound
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
  intro D
  refine ⟨drained_zero_barrier_admissible_infinite_cap X x hx.le, ?_,
    drained_zero_barrier_affine_jump_control X x hx.le w hw_affine,
    drained_zero_barrier_no_nonpositive_expected_bound X x hx w hwx q T hT⟩
  intro ω t _ ht
  have h0 := barrierStrategy_plus_linear_drain_ruinTime_zero X x hx.le ω
  simp only [D] at ht
  rw [h0] at ht
  exact absurd ht (not_lt.mpr bot_le)
