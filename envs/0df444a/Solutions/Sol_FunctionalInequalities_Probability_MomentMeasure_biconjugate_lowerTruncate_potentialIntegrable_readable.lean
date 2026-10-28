-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:17.887244+00:00
-- url     : https://prove2.me/submissions/f86d6032-46f1-4dce-958d-aa3f3328e25b

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Integrability
import Theorems.Thm_FunctionalInequalities_Analysis_lowerTruncate_convexification_readable

noncomputable section
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
section Truncation
variable {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
/-- A nonzero measure and the source a.e. finiteness give a real finite-domain
witness; probability normalization and centering are unnecessary. -/
theorem FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite (f : E → EReal) (hμ : μ ≠ 0)
    (hf : PotentialIntegrable f μ) : ∃ x, f x ≠ ⊤ := by
  let : NeZero μ := ⟨hμ⟩
  exact hf.2.1.exists
omit [MeasurableSpace E] in
/-- The actual extended truncation has the expected real value at every finite
input point. Infinite values are not silently converted to zero in this identity. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lowerTruncate_toReal_of_finite (f : E → EReal) (M : ℝ) (x : E)
    (ht : f x ≠ ⊤) (hb : f x ≠ ⊥) :
    (lowerTruncate f M x).toReal = max (f x).toReal (-M) := by
  change (max (f x) ((-M : ℝ) : EReal)).toReal = max (f x).toReal (-M)
  lift f x to ℝ using ⟨ht, hb⟩ with r hr
  rcases le_total r (-M) with h | h
  · simp only [EReal.toReal_coe,
      max_eq_right (EReal.coe_le_coe_iff.mpr h), max_eq_right h]
  · simp only [EReal.toReal_coe,
      max_eq_left (EReal.coe_le_coe_iff.mpr h), max_eq_left h]
/-- Lower truncation preserves the source admissibility for every real cutoff,
with no global finiteness, convexity or measurability assumption on the input. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lowerTruncate_potentialIntegrable [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hf : PotentialIntegrable f μ) :
    PotentialIntegrable (lowerTruncate f M) μ := by
  have hae : (fun x => (lowerTruncate f M x).toReal) =ᵐ[μ]
      (fun x => max (f x).toReal (-M)) := by
    filter_upwards [hf.2.1] with x hx
    exact lowerTruncate_toReal_of_finite f M x hx (hf.1 x)
  refine ⟨?_, ?_, ?_⟩
  · intro x
    exact ne_of_gt ((EReal.bot_lt_coe (-M)).trans_le (le_max_right _ _))
  · filter_upwards [hf.2.1] with x hx
    exact ne_of_lt (max_lt (Ne.lt_top hx) (EReal.coe_lt_top (-M)))
  · exact (hf.2.2.sup (integrable_const (-M))).congr hae.symm
end Truncation
section Convexification
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : MeasureTheory.Measure E}
/-- The actual biconjugate of the truncation is admissible. Its Borel real
restriction and domination are derived from lsc and the proved bounds, rather
than provided as additional integrability assumptions. -/
theorem solution [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hμ : μ ≠ 0) (hf : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ) :
    FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate f M))) μ := by
  have hfinite := FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite f hμ hf
  have hg := FunctionalInequalities.Probability.MomentMeasure.lowerTruncate_potentialIntegrable f M hf
  obtain ⟨hc, hls, _, hbounds, _⟩ := FunctionalInequalities.Analysis.lowerTruncate_convexification_readable f M hfinite
  have hfin : ∀ᵐ x ∂μ, FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate f M)) x ≠ ⊤ := by
    filter_upwards [hg.2.1] with x hx
    exact ne_of_lt ((hbounds x).2.trans_lt (Ne.lt_top hx))
  have hmeas : Measurable (fun x => (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate f M)) x).toReal) :=
    hls.measurable.ereal_toReal
  have hbnd : ∀ᵐ x ∂μ,
      ‖(FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate f M)) x).toReal‖ ≤
        ‖(FunctionalInequalities.Analysis.lowerTruncate f M x).toReal‖ + |M| := by
    filter_upwards [hfin, hg.2.1] with x hx hgt
    have hlo : -M ≤ (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate f M)) x).toReal := by
      simpa only [EReal.toReal_coe] using
        (EReal.toReal_le_toReal (hbounds x).1 (EReal.coe_ne_bot (-M)) hx)
    have hup := EReal.toReal_le_toReal (hbounds x).2 (hc.1 x) hgt
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have hM := le_abs_self M
      have hng := norm_nonneg ((FunctionalInequalities.Analysis.lowerTruncate f M x).toReal)
      linarith
    · have hgabs := le_abs_self ((FunctionalInequalities.Analysis.lowerTruncate f M x).toReal)
      rw [← Real.norm_eq_abs] at hgabs
      have hM := abs_nonneg M
      linarith
  exact ⟨hc.1, hfin, (hg.2.2.norm.add (integrable_const |M|)).mono'
    hmeas.aestronglyMeasurable hbnd⟩
