-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_esscher_weighted_negative_tail_of_finite_noAtoms
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T07:35:56.172794+00:00
-- url     : https://prove2.me/submissions/bedf9cec-b600-4346-b5c3-1819c0e9b8cf

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Analysis.Complex.Exponential
import Theorems.Thm_AvramDividend_Classical_continuousOn_measureReal_Iic_negative_of_finite_noAtoms
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set Topology
open scoped ENNReal

/-- Esscher weighting preserves atomlessness, so locally finite negative weighted tails
    depend continuously on a strictly positive jump-size threshold. -/
theorem solution
    (ν : Measure ℝ) [NullSingletonClass ν] (φ : ℝ)
    (hfinite : ∀ a : ℝ, a < 0 →
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Iic a) ≠ ⊤) :
    ContinuousOn (fun r : ℝ =>
      (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))).real (Iic (-r)))
      (Ioi (0 : ℝ)) := by
  let νφ : Measure ℝ :=
    ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))
  have hνφ : νφ ≪ ν := by
    dsimp [νφ]
    exact withDensity_absolutelyContinuous _ _
  letI : NullSingletonClass νφ := ⟨by
    intro a
    apply hνφ
    simp⟩
  have hcut : ∀ a : ℝ, a < 0 → νφ (Iic a) ≠ ⊤ := by
    intro a ha
    exact hfinite a ha
  have hcont : ContinuousOn (fun a : ℝ => νφ.real (Iic a)) (Iio (0 : ℝ)) :=
    continuousOn_measureReal_Iic_negative_of_finite_noAtoms νφ hcut
  have hneg : ContinuousOn (fun r : ℝ => -r) (Ioi (0 : ℝ)) :=
    (continuous_id.neg).continuousOn
  have hmaps : MapsTo (fun r : ℝ => -r) (Ioi (0 : ℝ)) (Iio (0 : ℝ)) := by
    intro r hr
    change -r < 0
    exact neg_lt_zero.mpr hr
  exact hcont.comp hneg hmaps
