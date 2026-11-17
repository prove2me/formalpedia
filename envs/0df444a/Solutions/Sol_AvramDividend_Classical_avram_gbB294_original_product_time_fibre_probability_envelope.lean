-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB294_original_product_time_fibre_probability_envelope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T08:08:02.424913+00:00
-- url     : https://prove2.me/submissions/21501b64-d380-42ff-a148-08ac6a97938e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB294_sfinite_product_time_fibre_probability_envelope
import Theorems.Thm_AvramDividend_Classical_avram_gbB294_nonsfinite_product_time_fibre_envelope
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by 
  classical
  by_cases hSF : SFinite P
  · letI : SFinite P := hSF
    exact AvramDividend.Classical.avram_gbB294_sfinite_product_time_fibre_probability_envelope
      P S hS g hFibre
  · exact AvramDividend.Classical.avram_gbB294_nonsfinite_product_time_fibre_envelope
      P hSF S hS g hFibre
