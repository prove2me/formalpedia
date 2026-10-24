-- Prove2me | solution 1 for FunctionalInequalities.Poincare.SmoothTest.holds_map_linearIsometryEquiv_iff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T18:05:46.533984+00:00
-- url     : https://prove2.me/submissions/6b91f735-a220-4eb9-8b7d-5ef21059d84e

import Definitions.Def_KLS408915f_FunctionalInequalities_Poincare_SmoothTest_Basic
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Probability.Moments.Variance
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_admissible_map_linearIsometryEquiv_iff_408915f
import Theorems.Thm_FunctionalInequalities_Poincare_SmoothTest_gradient_comp_projection_408915f

noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Poincare
end FunctionalInequalities.Poincare
open FunctionalInequalities FunctionalInequalities.Poincare
section
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities FunctionalInequalities.Poincare FunctionalInequalities.Poincare.SmoothTest
variable {E F : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
section CoordinateLift
variable (q : E →L[ℝ] F)
/-- The norm identity needed for coordinate energy; no division by dimension.
Source: local consequence of `gradient_comp_projection` and the isometric-adjoint hypothesis. -/
theorem FunctionalInequalities.Poincare.SmoothTest.norm_gradient_comp_projection {f : F → ℝ} {x : E}
    (hq : Isometry q.adjoint) (hf : DifferentiableAt ℝ f (q x)) :
    ‖gradient (f ∘ q) x‖ ^ 2 = ‖gradient f (q x)‖ ^ 2 := by
  rw [gradient_comp_projection_408915f q hf, hq.norm_map_of_map_zero (map_zero _)]
variable [MeasurableSpace E] [MeasurableSpace F]
  {ρ : Measure E} {μ : Measure F}
/-- Source: local helper combining `norm_gradient_comp_projection` with Mathlib's `integral_map`;
`Admissible` supplies the required finite-energy hypothesis. -/
theorem FunctionalInequalities.Poincare.SmoothTest.energy_comp_projection (hq : Isometry q.adjoint)
    (hmap : MeasurePreserving q ρ μ) {f : F → ℝ} (hf : Admissible μ f) :
    energy ρ (f ∘ q) = energy μ f := by
  have hdiff : Differentiable ℝ f := hf.smooth'.differentiable (by simp)
  have hint : AEStronglyMeasurable (fun y ↦ ‖gradient f y‖ ^ 2) (ρ.map q) := by
    rw [hmap.map_eq]
    exact hf.energy_integrable.aestronglyMeasurable
  rw [energy, energy, ← hmap.map_eq,
    integral_map hmap.measurable.aemeasurable hint]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x ↦
    norm_gradient_comp_projection q hq (hdiff _))
end CoordinateLift
section IsometryTransport
variable [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F]
variable (e : E ≃ₗᵢ[ℝ] F) (μ : Measure E) [IsProbabilityMeasure μ]
omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
private theorem FunctionalInequalities.Poincare.SmoothTest.measurePreserving_isometryEquiv :
    MeasurePreserving (⇑e) μ (μ.map e) :=
  ⟨e.continuous.measurable, rfl⟩
omit [MeasurableSpace E] [BorelSpace E] [MeasurableSpace F] [BorelSpace F] in
private theorem FunctionalInequalities.Poincare.SmoothTest.isometry_adjoint_isometryEquiv :
    Isometry (e : E →L[ℝ] F).adjoint := by
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  exact e.symm.isometry
omit [CompleteSpace E] [CompleteSpace F] [IsProbabilityMeasure μ] in
/-- Source: local helper from Mathlib's `MeasurePreserving.variance_fun_comp` for the law pushed
forward by the linear isometry equivalence. -/
theorem FunctionalInequalities.Poincare.SmoothTest.variance_map_linearIsometryEquiv {f : F → ℝ} (hf : MemLp f 2 (μ.map e)) :
    variance f (μ.map e) = variance (f ∘ e) μ := by
  simpa [Function.comp_def] using
    ((measurePreserving_isometryEquiv e μ).variance_fun_comp
      hf.aestronglyMeasurable.aemeasurable).symm
/-- Source: local consequence of `energy_comp_projection` and Mathlib's
`LinearIsometryEquiv.adjoint_eq_symm`, with the `Admissible` finite-energy hypothesis. -/
theorem FunctionalInequalities.Poincare.SmoothTest.energy_map_linearIsometryEquiv {f : F → ℝ} (hf : Admissible (μ.map e) f) :
    energy (μ.map e) f = energy μ (f ∘ e) :=
  have : IsProbabilityMeasure (μ.map ⇑e) :=
    Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  (energy_comp_projection (e : E →L[ℝ] F) (isometry_adjoint_isometryEquiv e)
    (measurePreserving_isometryEquiv e μ) hf).symm
namespace FunctionalInequalities.Poincare.SmoothTest
end FunctionalInequalities.Poincare.SmoothTest
open FunctionalInequalities.Poincare.SmoothTest in
/-- Source: local consequence of the admissibility, variance, and energy transport identities
above, applied to the repository's fixed-constant `Holds` definition. -/
theorem solution {C : ℝ} :
    FunctionalInequalities.Poincare.SmoothTest.Holds (μ.map e) C ↔ FunctionalInequalities.Poincare.SmoothTest.Holds μ C := by
  have hprob : IsProbabilityMeasure (μ.map ⇑e) :=
    Measure.isProbabilityMeasure_map e.continuous.measurable.aemeasurable
  constructor
  · intro h
    refine ⟨inferInstance, h.constant_nonneg, fun g hg ↦ ?_⟩
    have hgid : (g ∘ ⇑e.symm) ∘ ⇑e = g := funext fun x ↦ by
      simp [Function.comp]
    have hgF : FunctionalInequalities.Poincare.SmoothTest.Admissible (μ.map ⇑e) (g ∘ ⇑e.symm) := by
      apply (FunctionalInequalities.Poincare.SmoothTest.admissible_map_linearIsometryEquiv_iff_408915f e μ).mpr
      rwa [hgid]
    have hv := h.variance_le hgF
    rw [FunctionalInequalities.Poincare.SmoothTest.variance_map_linearIsometryEquiv e μ hgF.memLp_two,
      FunctionalInequalities.Poincare.SmoothTest.energy_map_linearIsometryEquiv e μ hgF, hgid] at hv
    exact hv
  · intro h
    refine ⟨hprob, h.constant_nonneg, fun f hf ↦ ?_⟩
    rw [FunctionalInequalities.Poincare.SmoothTest.variance_map_linearIsometryEquiv e μ hf.memLp_two,
      FunctionalInequalities.Poincare.SmoothTest.energy_map_linearIsometryEquiv e μ hf]
    exact h.variance_le ((FunctionalInequalities.Poincare.SmoothTest.admissible_map_linearIsometryEquiv_iff_408915f e μ).mp hf)
