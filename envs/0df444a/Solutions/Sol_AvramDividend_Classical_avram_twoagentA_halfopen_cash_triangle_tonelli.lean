-- Prove2me | solution 1 for AvramDividend.Classical.avram_twoagentA_halfopen_cash_triangle_tonelli
-- status  : ACCEPTED   (prove)
-- author  : @martelus trismortuus
-- created : 2026-11-26T02:40:25.1263+00:00
-- url     : https://prove2.me/submissions/de9096a6-8968-49fc-a4b9-33818e63558d

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem _root_.solution
    (μ : Measure ℝ) (T : ℝ≥0)
    (hfinite : μ (Ico (0 : ℝ) (T : ℝ)) ≠ ⊤)
    (k : ℝ → ℝ≥0∞) (hk : Measurable k) :
    (∫⁻ s in Ico (0 : ℝ) (T : ℝ),
      ∫⁻ u in Ioc (0 : ℝ) (T : ℝ),
        if s < u then k u else 0 ∂volume ∂μ) =
    (∫⁻ u in Ioc (0 : ℝ) (T : ℝ),
      k u * μ (Ico (0 : ℝ) u) ∂volume) := by
  have : IsFiniteMeasure (μ.restrict (Ico (0 : ℝ) (T : ℝ))) := by
    refine ⟨?_⟩
    rw [Measure.restrict_apply_univ]; exact lt_top_iff_ne_top.2 hfinite
  have hm : Measurable (Function.uncurry fun s u : ℝ => if s < u then k u else 0) :=
    Measurable.ite (measurableSet_lt measurable_fst measurable_snd) (hk.comp measurable_snd) measurable_const
  rw [lintegral_lintegral_swap hm.aemeasurable]
  refine setLIntegral_congr_fun measurableSet_Ioc fun u hu => ?_
  have e : (fun s : ℝ => if s < u then k u else 0) = (Iio u).indicator fun _ => k u := by
    funext s; simp [Set.indicator, Set.mem_Iio]
  rw [e, lintegral_indicator_const measurableSet_Iio, Measure.restrict_apply measurableSet_Iio]
  congr 2
  ext s
  simp only [mem_inter_iff, mem_Iio, mem_Ico]
  constructor
  · rintro ⟨h1, h2, _⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1, lt_of_lt_of_le h2 hu.2⟩

