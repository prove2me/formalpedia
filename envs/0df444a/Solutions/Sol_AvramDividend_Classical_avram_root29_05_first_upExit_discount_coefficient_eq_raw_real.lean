-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_05_first_upExit_discount_coefficient_eq_raw_real
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T16:33:42.586287+00:00
-- url     : https://prove2.me/submissions/5bfebcbb-4e5d-414a-853a-fded6b0967cd

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_upExit_before_controlledRuin_iff_rawExit
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

/-- On strict successful first upcrossing, the original ENNReal exit clock
has its genuine finite NNReal value, preserving the source discount. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a q : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxa : x ≤ a) :
    (let T := twoSidedExitUpTime X (a - x)
     let R := ruinTime X x (barrierStrategy X x a)
     ∫⁻ ω, if T ω < R ω then ENNReal.ofReal
       (Real.exp (-(q * ((T ω).toNNReal : ℝ)))) else 0 ∂P) =
    (let T := twoSidedExitUpTime X (a - x)
     ∫⁻ ω, if T ω < (⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)) then
       ENNReal.ofReal (Real.exp (-(q * (T ω).toReal))) else 0 ∂P) := by
  apply lintegral_congr
  intro ω
  let T : ℝ≥0∞ := twoSidedExitUpTime X (a - x) ω
  let R : ℝ≥0∞ := ruinTime X x (barrierStrategy X x a) ω
  let L : ℝ≥0∞ := ⨅ (t : ℝ≥0) (_ : X.X t ω < -x), (t : ℝ≥0∞)
  have hevent : T < R ↔ T < L := by
    simpa only [T, R, L, twoSidedExitUpTime] using
      barrierStrategy_upExit_before_controlledRuin_iff_rawExit X x a ha hx0 hxa ω
  change (if T < R then ENNReal.ofReal (Real.exp (-(q * (T.toNNReal : ℝ)))) else 0) =
    (if T < L then ENNReal.ofReal (Real.exp (-(q * T.toReal))) else 0)
  by_cases h : T < L
  · rw [if_pos h, if_pos (hevent.mpr h)]
    have hf : T ≠ ⊤ := ne_top_of_lt h
    have hu : (T.toNNReal : ℝ≥0∞) = T := ENNReal.coe_toNNReal hf
    rw [← hu]
    simp
  · rw [if_neg h, if_neg (fun hR => h (hevent.mp hR))]
