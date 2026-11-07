-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_jump8_zero_horizon_intrinsic_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:25:20.07465+00:00
-- url     : https://prove2.me/submissions/8860582f-051d-420e-83d7-ae9a3561733b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The literal intrinsic jump measure has no mass in the empty window (0,0]. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) :
    ∀ (k : ℕ),
      (∫ ω : Ω, Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (0 : ℝ≥0) ∧
          p.2 < -(1 / ((k : ℝ) + 1)) then
          ENNReal.ofReal (-p.2) else 0
        ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal)) ∂P) = 1 := by
  intro k
  letI : IsProbabilityMeasure P := X.isProbability
  have hzero (ω : Ω) :
      (∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ (0 : ℝ≥0) ∧
          p.2 < -(1 / ((k : ℝ) + 1)) then
          ENNReal.ofReal (-p.2) else 0
        ∂((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u, X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by
    have hfun :
        (fun p : ℝ≥0 × ℝ =>
          if 0 < p.1 ∧ p.1 ≤ (0 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1)) then
            ENNReal.ofReal (-p.2) else 0) = (fun _ => 0) := by
      funext p
      have hfalse :
          ¬ (0 < p.1 ∧ p.1 ≤ (0 : ℝ≥0) ∧
            p.2 < -(1 / ((k : ℝ) + 1))) := by
        intro h
        exact (not_lt_of_ge h.2.1) h.1
      exact if_neg hfalse
    rw [hfun]
    simp
  simp only [hzero]
  simp
