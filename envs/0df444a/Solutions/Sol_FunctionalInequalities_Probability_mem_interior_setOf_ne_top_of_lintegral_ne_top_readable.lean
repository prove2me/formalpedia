-- Prove2me | solution 1 for FunctionalInequalities.Probability.mem_interior_setOf_ne_top_of_lintegral_ne_top_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:38:21.554936+00:00
-- url     : https://prove2.me/submissions/43d53528-72c9-41e0-80bb-92fc3ada5746

import Definitions.Def_KLSModular_FunctionalInequalities_Probability_ConvexSupport

open MeasureTheory
open scoped RealInnerProductSpace
section EffectiveDomain
open MeasureTheory Set
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E]
omit [MeasurableSpace E] in
private lemma FunctionalInequalities.Probability.effective_domain_convex (φ : E → EReal)
    (hφ : Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)}) : Convex ℝ {x | φ x ≠ ⊤} := by
  have himage : (LinearMap.fst ℝ E ℝ) '' {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} = {x | φ x ≠ ⊤} := by
    ext x
    constructor
    · rintro ⟨⟨y,t⟩, hp, hxy⟩
      change y = x at hxy
      subst y
      change φ x ≤ (t : EReal) at hp
      exact (lt_of_le_of_lt hp (EReal.coe_lt_top t)).ne
    · intro hx
      refine ⟨(x,(φ x).toReal), ?_, rfl⟩
      exact EReal.le_coe_toReal hx
  rw [← himage]
  exact hφ.linear_image (LinearMap.fst ℝ E ℝ)
/-- An interior point of the convex hull of the support of a finite measure is interior to the effective domain of every
nonnegative extended-real potential with convex real epigraph and finite integral. -/
theorem solution [FiniteDimensional ℝ E] [BorelSpace E] (μ : Measure E) [IsFiniteMeasure μ] (x₀ : E) :
    x₀ ∈ interior (convexHull ℝ μ.support) →
      ∀ φ : E → EReal, (∀ x, 0 ≤ φ x) → Convex ℝ {p : E × ℝ | φ p.1 ≤ (p.2 : EReal)} →
        AEMeasurable (fun x => (φ x).toENNReal) μ →
        (∫⁻ x, (φ x).toENNReal ∂μ) ≠ ⊤ →
          x₀ ∈ interior {x | φ x ≠ ⊤} := by
  intro hx₀ φ _h_nonneg h_epi h_meas h_int
  let D : Set E := {x | φ x ≠ ⊤}
  have hD : Convex ℝ D := FunctionalInequalities.Probability.effective_domain_convex φ h_epi
  have h_ae : ∀ᵐ x ∂μ, x ∈ D := by
    filter_upwards [ae_lt_top' h_meas h_int] with x hx
    exact EReal.toENNReal_ne_top_iff.mp hx.ne
  have h_support : μ.support ⊆ closure D :=
    Measure.support_subset_of_isClosed isClosed_closure
      (h_ae.mono fun _ hx => subset_closure hx)
  have h_closed_span : closure D ⊆ (affineSpan ℝ D : Set E) :=
    closure_minimal (subset_affineSpan ℝ D)
      (affineSpan ℝ D).closed_of_finiteDimensional
  have h_support_span : affineSpan ℝ μ.support = ⊤ :=
    affineSpan_eq_top_of_nonempty_interior ⟨x₀,hx₀⟩
  have h_span : affineSpan ℝ D = ⊤ := by
    apply top_unique
    rw [← h_support_span]
    exact affineSpan_le.mpr (h_support.trans h_closed_span)
  have h_interior : (interior D).Nonempty :=
    hD.interior_nonempty_iff_affineSpan_eq_top.mpr h_span
  have h_hull : convexHull ℝ μ.support ⊆ closure D :=
    convexHull_min h_support hD.closure
  have hx_closure : x₀ ∈ interior (closure D) := interior_mono h_hull hx₀
  rwa [hD.interior_closure_eq_interior_of_nonempty_interior h_interior] at hx_closure
