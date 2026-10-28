-- Prove2me | solution 1 for FunctionalInequalities.Analysis.hasWeakDerivAlong_of_lipschitz_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:36.082778+00:00
-- url     : https://prove2.me/submissions/f54cfd3f-6c49-4ecb-adaf-dc8b6d421e30

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic

noncomputable section
open MeasureTheory
open scoped ContDiff
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
/-- A Lipschitz function has its almost-everywhere (Rademacher) derivative as weak derivative. -/
theorem solution {f : E → ℝ} {L : NNReal} (hf : LipschitzWith L f) (v : E) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong f (fun x => fderiv ℝ f x v) v := by
  have hline : LocallyIntegrable (fun x => lineDeriv ℝ f x v) (volume : Measure E) :=
    hf.locallyIntegrable_lineDeriv v
  have hdiff : ∀ᵐ x : E ∂(volume : Measure E), DifferentiableAt ℝ f x :=
    hf.ae_differentiableAt
  have hae : (fun x => lineDeriv ℝ f x v) =ᵐ[(volume : Measure E)]
      (fun x => fderiv ℝ f x v) := by
    filter_upwards [hdiff] with x hx
    exact hx.lineDeriv_eq_fderiv
  refine ⟨hf.continuous.locallyIntegrable, hline.congr hae, ?_⟩
  intro ψ hψ hψc
  obtain ⟨D, hψlip⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport hψc hψ (by simp)
  have hleft : (fun x => fderiv ℝ f x v * ψ x) =ᵐ[(volume : Measure E)]
      (fun x => lineDeriv ℝ f x v * ψ x) := by
    filter_upwards [hae] with x hx
    rw [hx]
  have hlineeq :
      (∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E)) =
        -(∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) := by
    calc
      ∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E) =
          ∫ x, lineDeriv ℝ ψ x (-v) * f x ∂(volume : Measure E) :=
        hf.integral_lineDeriv_mul_eq hψlip hψc v
      _ = ∫ x, -(f x * fderiv ℝ ψ x v) ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        have hx : DifferentiableAt ℝ ψ x :=
          (hψ.differentiable (by simp)).differentiableAt
        rw [hx.lineDeriv_eq_fderiv]
        simp [mul_comm]
      _ = -(∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) :=
        integral_neg _
  calc
    ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) =
        -(∫ x, lineDeriv ℝ f x v * ψ x ∂(volume : Measure E)) := by
      linarith [hlineeq]
    _ = -(∫ x, fderiv ℝ f x v * ψ x ∂(volume : Measure E)) := by
      rw [integral_congr_ae hleft]
