-- Prove2me | solution 1 for FunctionalInequalities.Analysis.HasWeakDerivAlong.congr_ae_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:27:27.286342+00:00
-- url     : https://prove2.me/submissions/56efac03-1a23-48cc-a603-67ca192e8dcc

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_WeakDerivative_Basic

noncomputable section
open MeasureTheory
open scoped ContDiff
universe u
/-- Weak directional derivatives are invariant under almost-everywhere
changes of both the function and its derivative. Local integrability is produced. -/
theorem solution {E : Type u}
    [instNormedAddCommGroup : NormedAddCommGroup E]
    [instInnerProductSpace : InnerProductSpace ℝ E]
    [instFiniteDimensional : FiniteDimensional ℝ E]
    [instMeasurableSpace : MeasurableSpace E] [instBorelSpace : BorelSpace E]
    {f f' g g' : E → ℝ} {v : E}
    (h : FunctionalInequalities.Analysis.HasWeakDerivAlong f g v)
    (hf : f =ᵐ[(volume : Measure E)] f')
    (hg : g =ᵐ[(volume : Measure E)] g') :
    FunctionalInequalities.Analysis.HasWeakDerivAlong f' g' v := by
  refine ⟨h.1.congr hf, h.2.1.congr hg, ?_⟩
  intro ψ hψ hψc
  have ef :
      (∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, f' x * fderiv ℝ ψ x v ∂(volume : Measure E) := by
    apply integral_congr_ae
    exact hf.mono (fun x hx => congrArg (fun r : ℝ => r * fderiv ℝ ψ x v) hx)
  have eg :
      (∫ x, g x * ψ x ∂(volume : Measure E)) =
        ∫ x, g' x * ψ x ∂(volume : Measure E) := by
    apply integral_congr_ae
    exact hg.mono (fun x hx => congrArg (fun r : ℝ => r * ψ x) hx)
  calc
    (∫ x, f' x * fderiv ℝ ψ x v ∂(volume : Measure E)) =
        ∫ x, f x * fderiv ℝ ψ x v ∂(volume : Measure E) := ef.symm
    _ = -∫ x, g x * ψ x ∂(volume : Measure E) := h.2.2 ψ hψ hψc
    _ = -∫ x, g' x * ψ x ∂(volume : Measure E) :=
      congrArg (fun r : ℝ => -r) eg
