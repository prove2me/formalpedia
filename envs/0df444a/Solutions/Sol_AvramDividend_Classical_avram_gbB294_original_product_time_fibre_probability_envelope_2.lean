-- Prove2me | solution 2 for AvramDividend.Classical.avram_gbB294_original_product_time_fibre_probability_envelope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T18:34:51.748497+00:00
-- url     : https://prove2.me/submissions/c8a2a445-de01-49d1-9c93-ec8710703569
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.MeasureTheory.Measure.Prod
import Theorems.Thm_AvramDividend_Classical_avram_gbB294_prod_vs_swapped_product_one_sided
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by
  calc
    (P.prod volume) S ≤ (volume.prod P) (Prod.swap ⁻¹' S) :=
      avram_gbB294_prod_vs_swapped_product_one_sided P S hS
    _ ≤ ∫⁻ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ∂volume := by
      simpa [Set.preimage, Prod.swap] using
        (Measure.prod_apply_le (μ := (volume : Measure ℝ)) (ν := P)
          (measurable_swap hS))
    _ ≤ ∫⁻ t : ℝ, g t ∂volume := lintegral_mono hFibre
