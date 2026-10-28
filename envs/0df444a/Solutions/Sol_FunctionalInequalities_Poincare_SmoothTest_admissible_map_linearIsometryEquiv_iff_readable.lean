-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.admissible_map_linearIsometryEquiv_iff_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T15:22:08.394829+00:00
-- url     : https://prove2.me/submissions/7f99753c-61e8-4730-b8f7-7d2c9c94cc01

import Definitions.Def_KLSModular_FunctionalInequalities_Poincare_SmoothTest_Transport
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_gradient_comp_projection_readable

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
section CoordinateLift
variable (q : E →L[ℝ] F)
omit [CompleteSpace E] [CompleteSpace F] in
/-- `C∞` regularity of a test lifted along a continuous linear projection.
Source: local helper from Mathlib's `ContDiff.comp` and continuous-linear-map smoothness. -/
theorem FunctionalInequalities.Poincare.SmoothTest.contDiff_comp_projection {f : F → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (f ∘ q) :=
  hf.comp q.contDiff
/-- The norm identity needed for coordinate energy; no division by dimension.
Source: local consequence of `gradient_comp_projection` and the isometric-adjoint hypothesis. -/
theorem FunctionalInequalities.Poincare.SmoothTest.norm_gradient_comp_projection {f : F → ℝ} {x : E}
    (hq : Isometry q.adjoint) (hf : DifferentiableAt ℝ f (q x)) :
    ‖gradient (f ∘ q) x‖ ^ 2 = ‖gradient f (q x)‖ ^ 2 := by
  rw [gradient_comp_projection_readable q hf, hq.norm_map_of_map_zero (map_zero _)]
variable [MeasurableSpace E] [MeasurableSpace F]
  {ρ : MeasureTheory.Measure E} {μ : MeasureTheory.Measure F}
omit [CompleteSpace E] [CompleteSpace F] in
/-- L² lifting retains its explicit L² hypothesis.
Source: local specialization of Mathlib's `MemLp.comp_measurePreserving`. -/
theorem FunctionalInequalities.Poincare.SmoothTest.memLp_comp_projection (hmap : MeasurePreserving q ρ μ)
    {f : F → ℝ} (hf : MemLp f 2 μ) : MemLp (f ∘ q) 2 ρ :=
  hf.comp_measurePreserving hmap
/-- Finite gradient energy is transported with explicit integrability evidence.
Source: local helper from `norm_gradient_comp_projection` and Mathlib's
`MeasurePreserving.integrable_comp_of_integrable`. -/
theorem FunctionalInequalities.Poincare.SmoothTest.integrable_gradient_comp_projection (hq : Isometry q.adjoint)
    (hmap : MeasurePreserving q ρ μ) {f : F → ℝ} (hf : Admissible μ f) :
    Integrable (fun x ↦ ‖gradient (f ∘ q) x‖ ^ 2) ρ := by
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  have h1 : Integrable ((fun y ↦ ‖gradient f y‖ ^ 2) ∘ q) ρ :=
    hmap.integrable_comp_of_integrable hf.energy_integrable
  refine h1.congr (Filter.Eventually.of_forall fun x ↦ ?_)
  exact (norm_gradient_comp_projection q hq (hdiff _)).symm
/-- Source: local helper assembling `contDiff_comp_projection`, `memLp_comp_projection`, and
`integrable_gradient_comp_projection` for the repository's `Admissible` class. -/
theorem FunctionalInequalities.Poincare.SmoothTest.Admissible.comp_projection (hq : Isometry q.adjoint)
    (hmap : MeasurePreserving q ρ μ) {f : F → ℝ} (hf : Admissible μ f) :
    Admissible ρ (f ∘ q) :=
  ⟨contDiff_comp_projection q hf.smooth', memLp_comp_projection q hmap hf.memLp_two,
    integrable_gradient_comp_projection q hq hmap hf⟩
end CoordinateLift
section IsometryTransport
variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
variable (e : E ≃ₗᵢ[ℝ] F) (μ : MeasureTheory.Measure E) [MeasureTheory.IsProbabilityMeasure μ]
omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
private theorem FunctionalInequalities.Poincare.SmoothTest.measurePreserving_isometryEquiv :
    MeasurePreserving (⇑e) μ (μ.map e) :=
  ⟨e.continuous.measurable, rfl⟩
omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem FunctionalInequalities.Poincare.SmoothTest.isometry_adjoint_isometryEquiv :
    Isometry (e : E →L[ℝ] F).adjoint := by
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  exact e.symm.isometry
/-- The forward test transport along a linear isometry equivalence. -/
private theorem FunctionalInequalities.Poincare.SmoothTest.admissible_comp_isometryEquiv {f : F → ℝ}
    (hf : Admissible (μ.map e) f) : Admissible μ (f ∘ e) :=
  have : IsProbabilityMeasure (μ.map ⇑e) :=
    Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  Admissible.comp_projection (e : E →L[ℝ] F) (isometry_adjoint_isometryEquiv e)
    (measurePreserving_isometryEquiv e μ) hf
/-- Exact test-domain correspondence for a linear isometry equivalence.
Source: local consequence of `Admissible.comp_projection` in both directions and
Mathlib's `LinearIsometryEquiv.adjoint_eq_symm`; this is not a change of test domain. -/
theorem solution {f : F → ℝ} :
    FunctionalInequalities.Poincare.SmoothTest.Admissible (μ.map e) f ↔ FunctionalInequalities.Poincare.SmoothTest.Admissible μ (f ∘ e) := by
  constructor
  · exact FunctionalInequalities.Poincare.SmoothTest.admissible_comp_isometryEquiv e μ
  · intro h
    have hprob : IsProbabilityMeasure (μ.map ⇑e) :=
      Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
    have hmm : (μ.map ⇑e).map ⇑e.symm = μ := by
      rw [Measure.map_map e.symm.continuous.measurable e.continuous.measurable]
      have hco : ⇑e.symm ∘ ⇑e = id := funext fun x ↦ e.symm_apply_apply x
      rw [hco, Measure.map_id]
    have h' : FunctionalInequalities.Poincare.SmoothTest.Admissible ((μ.map ⇑e).map ⇑e.symm) (f ∘ ⇑e) := by rwa [hmm]
    have h2 := FunctionalInequalities.Poincare.SmoothTest.admissible_comp_isometryEquiv e.symm (μ.map ⇑e) h'
    have hfe : (f ∘ ⇑e) ∘ ⇑e.symm = f := funext fun y ↦ by
      simp [Function.comp]
    rwa [hfe] at h2
