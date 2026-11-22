-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_public_original_bounded_physical_rectangle_mark_integrable_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T14:06:46.143133+00:00
-- url     : https://prove2.me/submissions/9d202d79-053a-4e9a-997f-c5799027ea43

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped Classical NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem solution
    (μ : Measure (ℝ≥0 × ℝ)) (T : ℝ≥0) (a b : ℝ)
    (ha : -1 ≤ a) (hb : b ≤ 0)
    (hFin : μ (Ioc (0 : ℝ≥0) T ×ˢ Ioc a b) < ⊤) :
    IntegrableOn (fun p : ℝ≥0 × ℝ => p.2)
      (Ioc (0 : ℝ≥0) T ×ˢ Ioc a b) μ := by
  classical
  let R : Set (ℝ≥0 × ℝ) := Ioc (0 : ℝ≥0) T ×ˢ Ioc a b
  have hBound : ∀ᵐ p ∂(μ.restrict R), ‖p.2‖ ≤ (1 : ℝ) := by
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod measurableSet_Ioc)] with p hp
    have hz := hp.2
    have hLow : -1 ≤ p.2 := le_trans ha hz.1.le
    have hUp : p.2 ≤ 0 := le_trans hz.2 hb
    have hAbs : |p.2| ≤ 1 := by
      rw [abs_of_nonpos hUp]
      linarith
    simpa only [Real.norm_eq_abs] using hAbs
  exact Measure.integrableOn_of_bounded (ne_of_lt hFin)
    measurable_snd.aestronglyMeasurable hBound
