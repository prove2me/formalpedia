-- Prove2me | solution 1 for AvramDividend.Classical.original_negative_tail_esscher_kernel_ac_positive_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T15:30:38.507462+00:00
-- url     : https://prove2.me/submissions/3f416bb7-c5bb-4d7a-a260-937568b17f46

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution (ν : Measure ℝ) (φ : ℝ) :
    let κ : Measure ℝ :=
      ((volume : Measure ℝ).withDensity
        (fun t : ℝ =>
          ENNReal.ofReal (Real.exp (-(φ * t))) * ν (Iio (-t)))).restrict
          (Ioi (0 : ℝ))
    κ (Iic (0 : ℝ)) = 0 ∧
    κ ≪ (volume : Measure ℝ) ∧
    (∀ x : ℝ, κ {x} = 0) := by
  let κ : Measure ℝ :=
    ((volume : Measure ℝ).withDensity
      (fun t : ℝ => ENNReal.ofReal (Real.exp (-(φ * t))) *
        ν (Iio (-t)))).restrict (Ioi (0 : ℝ))
  have hDisjoint : Iic (0 : ℝ) ∩ Ioi 0 = (∅ : Set ℝ) := by
    ext t
    simp only [mem_inter_iff, mem_Iic, mem_Ioi, mem_empty_iff_false, iff_false]
    intro ht
    exact (not_lt_of_ge ht.1) ht.2
  have hSupport : κ (Iic (0 : ℝ)) = 0 := by
    simp [κ, Measure.restrict_apply, hDisjoint]
  have hAC : κ ≪ (volume : Measure ℝ) :=
    Measure.absolutelyContinuous_restrict.trans
      (withDensity_absolutelyContinuous volume _)
  refine ⟨hSupport, hAC, ?_⟩
  intro x
  exact hAC (by simp)
