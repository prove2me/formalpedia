-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB294_nonsfinite_product_time_fibre_envelope
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:13:09.865923+00:00
-- url     : https://prove2.me/submissions/62df8182-1f75-4391-b605-1684303bbfdf
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB294_prod_vs_swapped_product_one_sided
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) (hNotSF : ¬ SFinite P)
    (S : Set (Ω × ℝ)) (hS : MeasurableSet S)
    (g : ℝ → ℝ≥0∞)
    (hFibre : ∀ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ≤ g t) :
    (P.prod volume) S ≤ ∫⁻ t : ℝ, g t ∂volume := by 
  classical
  have hSwap : MeasurableSet (Prod.swap ⁻¹' S) :=
    hS.preimage measurable_swap
  calc
    (P.prod volume) S ≤
        (volume.prod P) (Prod.swap ⁻¹' S) := by
      exact AvramDividend.Classical.avram_gbB294_prod_vs_swapped_product_one_sided P S hS
    _ ≤ ∫⁻ t : ℝ, P ((fun ω : Ω => (ω, t)) ⁻¹' S) ∂volume := by
      exact Measure.prod_apply_le hSwap
    _ ≤ ∫⁻ t : ℝ, g t ∂volume := by
      exact lintegral_mono hFibre
