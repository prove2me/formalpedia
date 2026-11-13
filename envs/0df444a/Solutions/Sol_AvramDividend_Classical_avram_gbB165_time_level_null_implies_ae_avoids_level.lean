-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB165_time_level_null_implies_ae_avoids_level
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T16:01:18.484197+00:00
-- url     : https://prove2.me/submissions/0dc0f72c-2613-465f-adbf-f9ef84664934

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

theorem solution
    (n : ℕ) (f : ℝ → ℝ) (b : ℝ)
    (hzero : volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ f t = b} = 0) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      f t ≠ b := by
  have hAE : ∀ᵐ t ∂(volume : Measure ℝ),
      ¬ (0 < t ∧ t < (n : ℝ) ∧ f t = b) := by
    apply (ae_iff).2
    simpa only [not_not] using hzero
  have hR : ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      ¬ (0 < t ∧ t < (n : ℝ) ∧ f t = b) :=
    ae_restrict_of_ae hAE
  filter_upwards [hR, ae_restrict_mem measurableSet_Ioo] with t ht htI
  intro hEq
  exact ht ⟨htI.1, htI.2, hEq⟩
