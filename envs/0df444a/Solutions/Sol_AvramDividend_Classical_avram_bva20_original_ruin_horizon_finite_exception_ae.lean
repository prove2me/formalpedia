-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva20_original_ruin_horizon_finite_exception_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T20:52:06.511469+00:00
-- url     : https://prove2.me/submissions/e41e3fcc-1520-4631-88de-21e3a1acb51c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
noncomputable section

/-- A physical time is almost surely distinct from each finite exceptional contact. -/
theorem solution
    (T τ : ℝ) :
    ∀ᵐ t : ℝ ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
      t ≠ 0 ∧ t ≠ T ∧ t ≠ τ := by
  have h0 : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ 0 :=
    (volume : Measure ℝ).ae_ne (0 : ℝ)
  have hT : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ T :=
    (volume : Measure ℝ).ae_ne T
  have hτ : ∀ᵐ t : ℝ ∂(volume : Measure ℝ), t ≠ τ :=
    (volume : Measure ℝ).ae_ne τ
  filter_upwards [h0, hT, hτ] with t ht0 htT htτ
  exact ⟨ht0, htT, htτ⟩
