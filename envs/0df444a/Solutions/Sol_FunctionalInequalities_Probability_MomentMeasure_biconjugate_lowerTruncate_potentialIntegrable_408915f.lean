-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.biconjugate_lowerTruncate_potentialIntegrable_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:26:49.514057+00:00
-- url     : https://prove2.me/submissions/83c8d3a7-de60-4be7-a84a-a14c64e4c428

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_Convex_Legendre
import Definitions.Def_KLS408915f_FunctionalInequalities_Probability_MomentMeasure_Basic
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.Normed.Module.Convex
import Mathlib.Analysis.SpecialFunctions.Log.ENNRealLogExp
import Mathlib.Data.EReal.Operations
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.Topology.Instances.EReal.Lemmas
import Mathlib.Topology.Semicontinuity.Basic
import Theorems.Thm_FunctionalInequalities_Analysis_lowerTruncate_convexification_408915f

noncomputable section
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Probability
end FunctionalInequalities.Probability
open FunctionalInequalities FunctionalInequalities.Probability
section
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities FunctionalInequalities.Probability FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Analysis
section
open MeasureTheory
open scoped ENNReal
section Truncation
variable {E : Type*} [MeasurableSpace E] {μ : Measure E}
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
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E}
namespace FunctionalInequalities.Probability.MomentMeasure
end FunctionalInequalities.Probability.MomentMeasure
open FunctionalInequalities.Probability.MomentMeasure in
/-- The actual biconjugate of the truncation is admissible. Its Borel real
restriction and domination are derived from lsc and the proved bounds, rather
than provided as additional integrability assumptions. -/
theorem solution [IsFiniteMeasure μ]
    (f : E → EReal) (M : ℝ) (hμ : μ ≠ 0) (hf : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable f μ) :
    FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.legendre (FunctionalInequalities.Analysis.lowerTruncate f M))) μ := by
  have hfinite := FunctionalInequalities.Probability.MomentMeasure.potentialIntegrable_exists_finite f hμ hf
  have hg := FunctionalInequalities.Probability.MomentMeasure.lowerTruncate_potentialIntegrable f M hf
  obtain ⟨hc, hls, _, hbounds, _⟩ := FunctionalInequalities.Analysis.lowerTruncate_convexification_408915f f M hfinite
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
