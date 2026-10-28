-- Prove2me | solution 1 for FunctionalInequalities.Probability.MomentMeasure.origin_mem_interior_domain_of_lower_bound_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:39:05.330416+00:00
-- url     : https://prove2.me/submissions/5ef846c1-801a-444b-8165-c5301811180e

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Coercivity
import Definitions.Def_KLSModular_FunctionalInequalities_Probability_MomentMeasure_Normalization
import Theorems.Thm_FunctionalInequalities_Analysis_convex_epigraph_affineSubtract_readable
import Theorems.Thm_FunctionalInequalities_Probability_MomentMeasure_affineSubtract_potentialIntegrable_readable
import Theorems.Thm_FunctionalInequalities_Probability_mem_interior_setOf_ne_top_of_lintegral_ne_top_readable

section
noncomputable section
section
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
section Integral
variable {E : Type*} [MeasurableSpace E] {μ : MeasureTheory.Measure E}
/-- Source admissibility and nonnegativity identify the actual extended integral,
including its a.e. finite guard; infinity is never totalized before this step. -/
theorem FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential (φ : E → EReal) (hφ : PotentialIntegrable φ μ)
    (hnn : ∀ x, 0 ≤ φ x) :
    AEMeasurable (fun x => (φ x).toENNReal) μ ∧
      (∫⁻ x, (φ x).toENNReal ∂μ) = ENNReal.ofReal (∫ x, (φ x).toReal ∂μ) ∧
      0 ≤ ∫ x, (φ x).toReal ∂μ := by
  have heq : (fun x => (φ x).toENNReal) =ᵐ[μ] (fun x => ENNReal.ofReal (φ x).toReal) := by
    filter_upwards [hφ.2.1] with x hx
    exact EReal.toENNReal_of_ne_top hx
  have hm := hφ.2.2.aemeasurable.ennreal_ofReal
  refine ⟨hm.congr heq.symm, ?_, integral_nonneg (fun x => EReal.toReal_nonneg (hnn x))⟩
  rw [lintegral_congr_ae heq]
  exact (ofReal_integral_eq_lintegral_ofReal hφ.2.2
    (Eventually.of_forall fun x => EReal.toReal_nonneg (hnn x))).symm
end Integral
end
end
end
end

noncomputable section
open FunctionalInequalities.Analysis
section
open MeasureTheory Filter Set
open scoped ENNReal Topology
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
/-- An actual constant lower bound reduces a signed convex potential to the
accepted nonnegative finite-near producer by an actual constant shift. -/
theorem solution (μ : Measure E) [IsFiniteMeasure μ]
    (h0 : (0 : E) ∈ interior (convexHull ℝ μ.support))
    (hfirst : Integrable (fun x : E => x) μ)
    (c : E → EReal) (hc : FunctionalInequalities.Analysis.ConvexPotential c) (hp : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable c μ)
    (M : ℝ) (hlower : ∀ x, ((-M : ℝ) : EReal) ≤ c x) :
    (0 : E) ∈ interior {x | c x ≠ ⊤} := by
  let g := FunctionalInequalities.Analysis.affineSubtract c 0 (-M)
  have hnn : ∀ x, 0 ≤ g x := by
    intro x
    change 0 ≤ c x - ((inner ℝ 0 x + -M : ℝ) : EReal)
    simp only [inner_zero_left, zero_add]
    exact (EReal.sub_nonneg (.inr (EReal.coe_ne_top _)) (.inr (EReal.coe_ne_bot _))).mpr (hlower x)
  have hg : FunctionalInequalities.Probability.MomentMeasure.PotentialIntegrable g μ := FunctionalInequalities.Probability.MomentMeasure.affineSubtract_potentialIntegrable_readable c 0 (-M) hp hfirst
  obtain ⟨hm, hlin, _⟩ := FunctionalInequalities.Probability.MomentMeasure.lintegral_nonneg_potential g hg hnn
  have hfin : (∫⁻ x, (g x).toENNReal ∂μ) ≠ ⊤ := by rw [hlin]; exact ENNReal.ofReal_ne_top
  have hint := FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top_readable
    μ 0 h0 g hnn (FunctionalInequalities.Analysis.convex_epigraph_affineSubtract_readable c 0 (-M) hc.2) hm hfin
  have hD : {x | g x ≠ ⊤} = {x | c x ≠ ⊤} := by
    ext x
    change (g x ≠ ⊤) ↔ (c x ≠ ⊤)
    by_cases hx : c x = ⊤
    · simp only [g, FunctionalInequalities.Analysis.affineSubtract, hx, EReal.top_sub_coe, ne_eq, not_true_eq_false]
    · have hgf : g x ≠ ⊤ := by
        change c x - ((inner ℝ 0 x + -M : ℝ) : EReal) ≠ ⊤
        rw [← EReal.coe_toReal hx (hc.1 x), ← EReal.coe_sub]
        exact EReal.coe_ne_top _
      exact iff_of_true hgf hx
  rwa [hD] at hint
