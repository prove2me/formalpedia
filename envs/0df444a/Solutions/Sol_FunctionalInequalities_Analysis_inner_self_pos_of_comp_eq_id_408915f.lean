-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inner_self_pos_of_comp_eq_id_408915f
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-23T15:43:10.521274+00:00
-- url     : https://prove2.me/submissions/54bbf4d6-1ddc-4d28-90a6-7659f4270328

import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.Normed.Operator.Banach

open scoped RealInnerProductSpace
section
namespace FunctionalInequalities
end FunctionalInequalities
open FunctionalInequalities
section
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities FunctionalInequalities.Analysis
section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
namespace FunctionalInequalities.Analysis
end FunctionalInequalities.Analysis
open FunctionalInequalities.Analysis in
/-- A right inverse of a strictly positive operator is strictly positive. -/
theorem solution (T B : E →L[ℝ] E)
    (hpos : ∀ v : E, v ≠ 0 → 0 < ⟪T v, v⟫)
    (hTB : T.comp B = ContinuousLinearMap.id ℝ E) {v : E} (hv : v ≠ 0) :
    0 < ⟪B v, v⟫ := by
  have hf (z : E) : T (B z) = z := by
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] using
      congrArg (fun L : E →L[ℝ] E => L z) hTB
  have hBv : B v ≠ 0 := by
    intro hh
    have hz := hf v
    rw [hh, map_zero] at hz
    exact hv hz.symm
  have hp := hpos (B v) hBv
  rw [hf] at hp
  rwa [real_inner_comm] at hp
