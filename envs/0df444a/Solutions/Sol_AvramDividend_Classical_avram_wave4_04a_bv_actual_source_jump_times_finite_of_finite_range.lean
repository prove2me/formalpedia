-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04a_bv_actual_source_jump_times_finite_of_finite_range
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T14:38:37.945574+00:00
-- url     : https://prove2.me/submissions/086589d8-35f6-4bc7-9d39-4fa37711925e

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_bv_actual_strict_residual_jump_times_finite_of_finite_range
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/--
Finite range of the genuine source BV Lévy residual implies finitely many
actual nonzero source-X jumps on any bounded horizon, P-almost surely.
Both source-path provider theorems are canonically Proved.
-/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (T : ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∃ S : Finset ℝ,
      ∀ t : ℝ≥0, t ≤ T →
        (t : ℝ) * X.drift - X.X t ω ∈ S) :
    ∀ᵐ ω ∂P,
      {t : ℝ≥0 |
        t ≤ T ∧ 0 < t ∧
          X.X t ω -
            Function.leftLim (fun u : ℝ≥0 => X.X u ω) t ≠ 0}.Finite := by
  filter_upwards
    [avram_wave4_04a_bv_actual_strict_residual_jump_times_finite_of_finite_range
      X hBV T hRange]
    with ω hω
  apply hω.subset
  rintro t ⟨htT, htpos, hmark⟩
  exact ⟨htT, htpos,
    (avram_wave4_04a_actual_source_nonzero_jump_iff_strict_drift_residual_jump
      X ω t htpos).2 hmark⟩
