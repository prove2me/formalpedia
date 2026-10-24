-- Prove2me | solution 1 for FunctionalInequalities.Analysis.HasWeakDerivAlong.mul_contDiff_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:53:24.773+00:00
-- url     : https://prove2.me/submissions/022094e7-c6ac-432f-bf61-dfbcb60b63f6

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_WeakDerivative_Basic
import Mathlib
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.Basic
import Mathlib.Analysis.Calculus.Rademacher
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.MeasureTheory.Function.ContinuousMapDense
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.SpecificCodomains.Pi

noncomputable section
open MeasureTheory
open scoped ContDiff
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
namespace FunctionalInequalities.Analysis.HasWeakDerivAlong
end FunctionalInequalities.Analysis.HasWeakDerivAlong
open FunctionalInequalities.Analysis.HasWeakDerivAlong in
/-- Product rule with a `C¹` multiplier of compact support. -/
theorem solution {f g : E → ℝ} {v : E} (h : FunctionalInequalities.Analysis.HasWeakDerivAlong f g v)
    {χ : E → ℝ} (hχ : ContDiff ℝ 1 χ) (hχc : HasCompactSupport χ) :
    FunctionalInequalities.Analysis.HasWeakDerivAlong (fun x => χ x * f x) (fun x => χ x * g x + fderiv ℝ χ x v * f x) v := by
  have hχd : Continuous (fun x => fderiv ℝ χ x v) :=
    (hχ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hχdc : HasCompactSupport (fun x => fderiv ℝ χ x v) := by
    change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ χ)
    exact (hχc.fderiv ℝ).comp_left (by simp)
  have hχf : LocallyIntegrable (fun x => χ x * f x) (volume : Measure E) := by
    simpa [mul_comm] using h.1.continuous_mul hχ.continuous
  have hχg : LocallyIntegrable (fun x => χ x * g x) (volume : Measure E) := by
    simpa [mul_comm] using h.2.1.continuous_mul hχ.continuous
  have hχdf : LocallyIntegrable (fun x => fderiv ℝ χ x v * f x)
      (volume : Measure E) := by
    simpa [mul_comm] using h.1.continuous_mul hχd
  refine ⟨hχf, hχg.add hχdf, ?_⟩
  intro ψ hψ hψc
  have hψd : Continuous (fun x => fderiv ℝ ψ x v) :=
    (hψ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hψdc : HasCompactSupport (fun x => fderiv ℝ ψ x v) := by
    change HasCompactSupport ((fun L : E →L[ℝ] ℝ => L v) ∘ fderiv ℝ ψ)
    exact (hψc.fderiv ℝ).comp_left (by simp)
  have iA : Integrable
      (fun x => (χ x * f x) * fderiv ℝ ψ x v) (volume : Measure E) := by
    have hi := hχf.integrable_smul_left_of_hasCompactSupport hψd hψdc
    convert hi using 1
    funext x
    ring
  have iB : Integrable
      (fun x => (f x * ψ x) * fderiv ℝ χ x v) (volume : Measure E) := by
    have hi := h.1.continuous_mul hψ.continuous
      |>.integrable_smul_left_of_hasCompactSupport hχd hχdc
    convert hi using 1
    funext x
    ring
  have iC : Integrable
      (fun x => (χ x * g x) * ψ x) (volume : Measure E) := by
    have hi := hχg.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    convert hi using 1
    funext x
    ring
  have iD : Integrable
      (fun x => (fderiv ℝ χ x v * f x) * ψ x) (volume : Measure E) := by
    have hi := hχdf.integrable_smul_left_of_hasCompactSupport hψ.continuous hψc
    convert hi using 1
    funext x
    ring
  have hderiv : ∀ x,
      fderiv ℝ (fun y => χ y * ψ y) x v =
        χ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ χ x v := by
    intro x
    change (fderiv ℝ (χ * ψ) x) v =
      χ x * fderiv ℝ ψ x v + ψ x * fderiv ℝ χ x v
    rw [fderiv_mul
      ((hχ.differentiable (by simp)).differentiableAt)
      ((hψ.differentiable (by simp)).differentiableAt)]
    simp [smul_eq_mul]
  have hsum :
      (∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E)) +
          (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
        -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) := by
    calc
      (∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E)) +
            (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
          ∫ x, ((χ x * f x) * fderiv ℝ ψ x v +
            (f x * ψ x) * fderiv ℝ χ x v) ∂(volume : Measure E) :=
        (integral_add iA iB).symm
      _ = ∫ x, f x * fderiv ℝ (fun y => χ y * ψ y) x v ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        rw [hderiv x]
        ring
      _ = -∫ x, g x * (χ x * ψ x) ∂(volume : Measure E) :=
        h.2.2 (fun x => χ x * ψ x) (hχ.mul hψ) hχc.mul_right
      _ = -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) := by
        congr 1
        apply integral_congr_ae
        filter_upwards [] with x
        ring
  have hBD :
      (∫ x, (f x * ψ x) * fderiv ℝ χ x v ∂(volume : Measure E)) =
        ∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
    apply integral_congr_ae
    filter_upwards [] with x
    ring
  have hCD :
      (∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) =
        (∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) +
          (∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) := by
    calc
      ∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) =
          ∫ x, ((χ x * g x) * ψ x + (fderiv ℝ χ x v * f x) * ψ x) ∂(volume : Measure E) := by
        apply integral_congr_ae
        filter_upwards [] with x
        ring
      _ = (∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) +
          (∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E)) :=
        integral_add iC iD
  calc
    ∫ x, (χ x * f x) * fderiv ℝ ψ x v ∂(volume : Measure E) =
        -(∫ x, (χ x * g x) * ψ x ∂(volume : Measure E)) -
          ∫ x, (fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
      linarith [hsum, hBD]
    _ = -∫ x, (χ x * g x + fderiv ℝ χ x v * f x) * ψ x ∂(volume : Measure E) := by
      rw [hCD]
      ring
