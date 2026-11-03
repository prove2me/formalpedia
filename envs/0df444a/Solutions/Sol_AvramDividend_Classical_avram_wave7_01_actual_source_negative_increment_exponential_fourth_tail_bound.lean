-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_actual_source_negative_increment_exponential_fourth_tail_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T23:47:35.968541+00:00
-- url     : https://prove2.me/submissions/d30f6f47-b824-4113-b247-ceb6253fa338




import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Exponential fourth-power Markov bound on the unchanged source increment. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (h : ℝ≥0) (ε θ : ℝ) (hε : 0 < ε) (hθ : 0 < θ)
    (hXm : Measurable (X.X h)) :
    (ENNReal.ofReal ((1 - Real.exp (-θ * ε)) ^ 4)) *
      P {ω : Ω | X.X h ω ≤ -ε} ≤
    (∫⁻ ω, ENNReal.ofReal
      ((Real.exp (θ * X.X h ω) - 1) ^ 4) ∂P) := by
  classical
  let c : ℝ≥0∞ := ENNReal.ofReal ((1 - Real.exp (-θ * ε)) ^ 4)
  let f : Ω → ℝ≥0∞ := fun ω =>
    ENNReal.ofReal ((Real.exp (θ * X.X h ω) - 1) ^ 4)
  have hf : Measurable f := by
    dsimp [f]
    exact ENNReal.measurable_ofReal.comp
      (((Real.measurable_exp.comp (measurable_const.mul hXm)).sub
        measurable_const).pow_const 4)
  have hSub :
      {ω : Ω | X.X h ω ≤ -ε} ⊆ {ω : Ω | c ≤ f ω} := by
    intro ω hω
    have hθY : θ * X.X h ω ≤ -θ * ε := by
      calc
        θ * X.X h ω ≤ θ * (-ε) :=
          mul_le_mul_of_nonneg_left hω (le_of_lt hθ)
        _ = -θ * ε := by ring
    have hExp :
        Real.exp (θ * X.X h ω) ≤ Real.exp (-θ * ε) :=
      Real.exp_le_exp.mpr hθY
    have hProd : 0 < θ * ε := mul_pos hθ hε
    have hNeg : -θ * ε ≤ 0 := by
      nlinarith only [hProd]
    have hExpOne : Real.exp (-θ * ε) ≤ 1 := by
      simpa using (Real.exp_le_exp.mpr hNeg)
    have hPos : 0 ≤ 1 - Real.exp (-θ * ε) := by linarith
    have hDiff :
        1 - Real.exp (-θ * ε) ≤
          1 - Real.exp (θ * X.X h ω) := by linarith
    have hPow :
        (1 - Real.exp (-θ * ε)) ^ 4 ≤
          (1 - Real.exp (θ * X.X h ω)) ^ 4 :=
      pow_le_pow_left₀ hPos hDiff 4
    have hFlip :
        (1 - Real.exp (θ * X.X h ω)) ^ 4 =
          (Real.exp (θ * X.X h ω) - 1) ^ 4 := by ring
    have hRewardBound :
        (1 - Real.exp (-θ * ε)) ^ 4 ≤
          (Real.exp (θ * X.X h ω) - 1) ^ 4 :=
      hPow.trans_eq hFlip
    exact ENNReal.ofReal_le_ofReal hRewardBound
  change c * P {ω : Ω | X.X h ω ≤ -ε} ≤ ∫⁻ ω, f ω ∂P
  calc
    c * P {ω : Ω | X.X h ω ≤ -ε} ≤
        c * P {ω : Ω | c ≤ f ω} :=
      by
        gcongr
    _ ≤ ∫⁻ ω, f ω ∂P :=
      MeasureTheory.mul_meas_ge_le_lintegral hf c