-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_assist_negative_cdf_determines_separated_borel
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T08:39:43.399701+00:00
-- url     : https://prove2.me/submissions/40443063-7b14-4ff3-a87f-411f19c520b0

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- Halfline cut rates identify every separated Borel subset, including atoms at endpoints. -/
theorem solution
    (μ ν : Measure ℝ)
    (hμBand : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) < ⊤)
    (hCuts : ∀ δ : ℝ, 0 < δ → μ (Iic (-δ)) = ν (Iic (-δ)))
    (B : Set ℝ) (hB : MeasurableSet B)
    (ε : ℝ) (hε : 0 < ε) (hBsep : B ⊆ Iic (-ε)) :
    μ B = ν B := by
  classical
  have hμFinite : μ (Iic (-ε)) ≠ ⊤ :=
    ne_of_lt (hμBand ε hε)
  haveI : IsFiniteMeasure (μ.restrict (Iic (-ε))) :=
    (isFiniteMeasure_restrict).2 hμFinite
  have hCDF : ∀ a : ℝ,
      (μ.restrict (Iic (-ε))) (Iic a) =
        (ν.restrict (Iic (-ε))) (Iic a) := by
    intro a
    rw [Measure.restrict_apply measurableSet_Iic,
      Measure.restrict_apply measurableSet_Iic]
    by_cases ha : a ≤ -ε
    · have haNeg : a < 0 := by linarith
      have hi : Iic a ∩ Iic (-ε) = Iic a :=
        inter_eq_left.mpr (Iic_subset_Iic.mpr ha)
      simpa only [hi, neg_neg] using (hCuts (-a) (by linarith))
    · have ha' : -ε ≤ a := le_of_not_ge ha
      have hi : Iic a ∩ Iic (-ε) = Iic (-ε) :=
        inter_eq_right.mpr (Iic_subset_Iic.mpr ha')
      simpa only [hi] using (hCuts ε hε)
  have hEqual : μ.restrict (Iic (-ε)) = ν.restrict (Iic (-ε)) :=
    Measure.ext_of_Iic _ _ hCDF
  have hEval := congrArg (fun κ : Measure ℝ => κ B) hEqual
  have hInter : B ∩ Iic (-ε) = B := inter_eq_left.mpr hBsep
  simpa only [Measure.restrict_apply hB, hInter] using hEval
