-- Prove2me | solution 1 for FunctionalInequalities.Analysis.BakryEmery.integrable_weightedLaplacian_gamma_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:25:29.320011+00:00
-- url     : https://prove2.me/submissions/44496929-b765-4fc0-904b-53e5cc57430e

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_BakryEmery_Curvature

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
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

section
noncomputable section
open InnerProductSpace
open scoped ContDiff RealInnerProductSpace
section
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

noncomputable section
open MeasureTheory InnerProductSpace
open scoped ContDiff RealInnerProductSpace
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]
variable [MeasurableSpace E] [BorelSpace E] (m : MeasureTheory.Measure E) [m.IsAddHaarMeasure]
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
