-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_original_finiteactivity_unconditional_void_negative_annulus_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:50:59.650258+00:00
-- url     : https://prove2.me/submissions/893969e6-30d6-4681-8de0-efa9b502c22f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_levy_jumpmark_joint_measurable
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_void_negative_mark_annulus_from_physical_event_20261114
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual finite-activity original marked jump count eventually avoids each shrinking negative band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      ∃ N : ℕ, ∀ n ≥ N,
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc 0 T ×ˢ Ioo (-(1 / ((n : ℝ) + 1))) (0 : ℝ)) = 0 := by
  have hMark : ∀ ω : Ω, Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)) := by
    intro ω
    have hSect : Measurable (fun u : ℝ≥0 => (u, ω)) :=
      measurable_id.prodMk measurable_const
    have hJ : Measurable (fun u : ℝ≥0 =>
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u) :=
      (avram_wave4_04a_actual_levy_jumpmark_joint_measurable X).comp hSect
    exact measurable_id.prodMk hJ
  exact avram_a27_original_void_negative_mark_annulus_from_physical_event_20261114
    X hFinite hMark
