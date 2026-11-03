-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_02_original_prejump_valid_finite_source_mark_discounted_C1_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T13:15:02.262017+00:00
-- url     : https://prove2.me/submissions/4e41571b-61be-4656-ab9f-3366eae9092b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical
noncomputable section

/-- The original finite family of negative source jumps, with actual
pre-source controlled reserves in the closed positive cap, contributes a
nonpositive discounted HJB value-jump sum, including ruin-overshooting marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ v < 0, w v = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C})
    (hw_grad : ∀ v : ℝ, 0 < v → ENNReal.ofReal v < C →
      1 ≤ deriv w v)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (q : ℝ)
    (S : Finset ℝ≥0)
    (hValid : ∀ t ∈ S,
      X.X t ω ≤ Function.leftLim (fun s : ℝ≥0 => X.X s ω) t ∧
      0 ≤ x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω ∧
      ENNReal.ofReal
        (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t - D t ω) ≤ C) :
    (∑ t ∈ S,
      (Real.exp (-(q * (t : ℝ))) *
        (w (x + X.X t ω - D t ω) -
          w (x + Function.leftLim (fun s : ℝ≥0 => X.X s ω) t -
            D t ω)))) ≤ 0 := by
  apply Finset.sum_nonpos
  intro t ht
  obtain ⟨hMark, hb, hbC⟩ := hValid t ht
  have hDrop :=
    avram_wave7_02_original_negative_source_jump_weak_C1_value_monotone_all_crossings
      X C hC w hw_cont hw0 hw_neg hw_smooth hw_grad
      x D ω t hMark hb hbC
  exact mul_nonpos_of_nonneg_of_nonpos
    (le_of_lt (Real.exp_pos _)) (sub_nonpos.mpr hDrop)
