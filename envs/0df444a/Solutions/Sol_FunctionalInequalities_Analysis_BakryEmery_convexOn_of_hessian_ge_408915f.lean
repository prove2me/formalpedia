-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.convexOn_of_hessian_ge_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:42:09.821422+00:00
-- url     : https://prove2.me/submissions/4807f79d-c2e2-4134-957b-1095aa4d91e3

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Gradient.Basic
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Measure.Tilted

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities FunctionalInequalities.Analysis FunctionalInequalities.Analysis.BakryEmery
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
omit [CompleteSpace E] [FiniteDimensional ℝ E] in
/-- A `C²` potential whose Hessian is bounded below by `ρ ≥ 0` is convex. -/
theorem solution {U : E → ℝ} (hU : ContDiff ℝ 2 U) {ρ : ℝ} (hρ : 0 ≤ ρ)
    (hH : ∀ x v, ρ * ‖v‖ ^ 2 ≤ bilinearIteratedFDerivTwo ℝ U x v v) :
    ConvexOn ℝ Set.univ U := by
  have hline :
      ∀ (x v : E), ConvexOn ℝ Set.univ (fun t : ℝ => U (x + t • v)) := by
    intro x v
    let g : ℝ → ℝ := fun t => U (x + t • v)
    have hg : ContDiff ℝ 2 g := by
      dsimp [g]
      exact hU.comp (by fun_prop)
    have hg' : ContDiff ℝ (1 + 1) g := by
      norm_num
      exact hg
    have hgd : ContDiff ℝ 1 (deriv g) := by
      exact (contDiff_succ_iff_deriv.mp hg').2.2
    refine convexOn_of_deriv2_nonneg' convex_univ
      ((hg.differentiable (by norm_num)).differentiableOn)
      ((hgd.differentiable (by norm_num)).differentiableOn) ?_
    intro t ht
    have hshift :
        deriv (deriv (fun s : ℝ => g (s + t))) 0 =
          deriv (deriv g) t := by
      have h₁ :
          deriv (fun s : ℝ => g (s + t)) =
            (fun s => deriv g (s + t)) := by
        funext s
        rw [deriv_comp_add_const]
      rw [h₁, deriv_comp_add_const]
      simp
    have hline₂ :
        (fun s : ℝ => g (s + t)) =
          (fun s : ℝ => U ((x + t • v) + s • v)) := by
      funext s
      dsimp [g]
      congr 1
      module
    have hsecond :
        deriv (deriv g) t =
          bilinearIteratedFDerivTwo ℝ U (x + t • v) v v := by
      rw [← hshift, hline₂]
      exact FunctionalInequalities.Analysis.BakryEmery.deriv_deriv_line hU (x + t • v) v
    have hnonneg : 0 ≤ deriv (deriv g) t := by
      rw [hsecond]
      exact
        le_trans
          (mul_nonneg hρ (sq_nonneg ‖v‖))
          (hH (x + t • v) v)
    simpa [Function.iterate_succ_apply, Function.iterate_zero_apply, g] using hnonneg
  refine ⟨convex_univ, ?_⟩
  intro a ha b hb α β hα hβ hαβ
  have h := hline a (b - a)
  have h' :=
    h.2 (show (0 : ℝ) ∈ Set.univ by simp)
      (show (1 : ℝ) ∈ Set.univ by simp) hα hβ hαβ
  have hα' : α = 1 - β := by
    linarith
  have hab : α • a + β • b = a + β • (b - a) := by
    rw [hα']
    module
  rw [hab]
  simpa [hα', smul_eq_mul] using h'
