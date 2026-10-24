-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T14:46:12.534955+00:00
-- url     : https://prove2.me/submissions/a42d4186-eb8b-4c33-96ee-5a0a73d8c76e

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

section
noncomputable section
open InnerProductSpace
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
section DifferentialTools
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gradient
variable [CompleteSpace E]
/-- The gradient of a `C^n` function is `C^m` when `m + 1 ≤ n`. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_gradient {f : E → ℝ} {n m : WithTop ℕ∞} (hf : ContDiff ℝ n f) (hmn : m + 1 ≤ n) :
    ContDiff ℝ m (gradient f) :=
  (toDual ℝ E).symm.contDiff.comp (hf.fderiv_right hmn)
end Gradient
end DifferentialTools
end
end
end
end
end

section
noncomputable section
open InnerProductSpace
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
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Gamma
variable [CompleteSpace E]
theorem FunctionalInequalities.Analysis.BakryEmery.gamma_apply (f g : E → ℝ) (x : E) : gamma f g x = ⟪gradient f x, gradient g x⟫ := rfl
/-- Regularity of the carré du champ: `C^{n+1}` data give a `C^n` carré du champ. -/
theorem FunctionalInequalities.Analysis.BakryEmery.contDiff_gamma {n p q : WithTop ℕ∞} {f g : E → ℝ} (hf : ContDiff ℝ p f)
    (hg : ContDiff ℝ q g) (hp : n + 1 ≤ p) (hq : n + 1 ≤ q) : ContDiff ℝ n (gamma f g) :=
  ContDiff.inner ℝ (contDiff_gradient hf hp) (contDiff_gradient hg hq)
/-- The carré du champ inherits the compact support of its first argument. -/
theorem FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gamma_left {f : E → ℝ} (g : E → ℝ) (hfc : HasCompactSupport f) :
    HasCompactSupport (gamma f g) := by
  refine (hasCompactSupport_gradient hfc).mono fun x hx => ?_
  intro h0
  apply hx
  simp [gamma_apply, h0]
variable [FiniteDimensional ℝ E]
end Gamma
end
end
end
end
end

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
variable [MeasurableSpace E] [BorelSpace E] (m : Measure E) [m.IsAddHaarMeasure]
namespace FunctionalInequalities.Analysis.BakryEmery
end FunctionalInequalities.Analysis.BakryEmery
open FunctionalInequalities.Analysis.BakryEmery in
omit [m.IsAddHaarMeasure] in
/-- `ℒ Γ(f)` is integrable against `m.tilted (-U)` for compactly supported `C³` functions `f`. -/
theorem solution {U f : E → ℝ} (hU : ContDiff ℝ 2 U)
    (hf : ContDiff ℝ 3 f) (hfc : HasCompactSupport f) :
    MeasureTheory.Integrable (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U (fun y => FunctionalInequalities.Analysis.BakryEmery.gamma f f y) x)
      (m.tilted (-U)) := by
  have hgamma : ContDiff ℝ 2 (FunctionalInequalities.Analysis.BakryEmery.gamma f f) := by
    exact FunctionalInequalities.Analysis.BakryEmery.contDiff_gamma (n := 2) hf hf (by norm_num) (by norm_num)
  have hcont :
      Continuous (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U (fun y => FunctionalInequalities.Analysis.BakryEmery.gamma f f y) x) := by
    simpa using
      (FunctionalInequalities.Analysis.BakryEmery.continuous_weightedLaplacian (U := U) (f := FunctionalInequalities.Analysis.BakryEmery.gamma f f)
        (hU.of_le (by norm_num)) hgamma)
  have hcompact :
      HasCompactSupport
        (fun x => FunctionalInequalities.Analysis.BakryEmery.weightedLaplacian U (fun y => FunctionalInequalities.Analysis.BakryEmery.gamma f f y) x) := by
    simpa using
      (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_weightedLaplacian U
        (FunctionalInequalities.Analysis.BakryEmery.hasCompactSupport_gamma_left f hfc))
  exact hcont.integrable_of_hasCompactSupport hcompact
