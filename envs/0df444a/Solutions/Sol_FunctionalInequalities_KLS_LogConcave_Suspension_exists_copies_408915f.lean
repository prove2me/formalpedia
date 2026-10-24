-- Prove2me | solution 1 for FunctionalInequalities.KLS.LogConcave.Suspension.exists_copies_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T17:57:31.853792+00:00
-- url     : https://prove2.me/submissions/275434a6-da2a-48cf-8434-81bfc5f733f5

import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Bochner_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Calculus
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Gamma
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_IntegrationByParts_Basic
import Definitions.Def_KLS408915f_FunctionalInequalities_Analysis_BakryEmery_Laplacian
import Definitions.Def_KLS408915f_FunctionalInequalities_KLS_BKL_Suspension_Basic
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
open scoped ContDiff
open FunctionalInequalities.Analysis.BakryEmery
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.KLS
end FunctionalInequalities.KLS
open FunctionalInequalities FunctionalInequalities.KLS
section
namespace FunctionalInequalities.KLS.LogConcave
end FunctionalInequalities.KLS.LogConcave
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave
section
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities FunctionalInequalities.KLS FunctionalInequalities.KLS.LogConcave FunctionalInequalities.KLS.LogConcave.Suspension
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.KLS.LogConcave.Suspension
end FunctionalInequalities.KLS.LogConcave.Suspension
open FunctionalInequalities.KLS.LogConcave.Suspension in
/-- A positive finite number of copies satisfies (110) for any positive curvature and finite
nonnegative Hessian bound. -/
theorem solution {a beta M : ℝ} (ha : 0 < a) (hbeta : 0 ≤ beta) (hM : 0 ≤ M) :
    ∃ N : ℕ, 0 < N ∧ beta / Real.sqrt N * M ≤ a := by
  obtain ⟨N, hN⟩ := exists_nat_gt ((beta * M / a) ^ 2 + 1)
  have hNpos : 0 < N := by
    have : (0 : ℝ) < N := by nlinarith [sq_nonneg (beta * M / a)]
    exact_mod_cast this
  have hspos : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hNpos)
  have hs : (Real.sqrt (N : ℝ)) ^ 2 = N := Real.sq_sqrt (by positivity)
  have hratio : 0 ≤ beta * M / a := div_nonneg (mul_nonneg hbeta hM) ha.le
  have hsmall : beta * M / a ≤ Real.sqrt (N : ℝ) := by nlinarith
  have hmul : beta * M ≤ a * Real.sqrt (N : ℝ) := by
    have := (div_le_iff₀ ha).1 hsmall
    nlinarith
  refine ⟨N, hNpos, ?_⟩
  rw [div_mul_eq_mul_div, div_le_iff₀ hspos]
  exact hmul
