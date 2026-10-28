-- Prove2me | solution 1 for FunctionalInequalities.Analysis.inner_self_pos_of_comp_eq_id_readable
-- status  : ACCEPTED   (prove)
-- author  : @Lazyfill
-- created : 2026-10-26T13:40:02.469635+00:00
-- url     : https://prove2.me/submissions/e96e7c2e-4ad5-43c6-a98e-6e9f76f1643b

import Definitions.Def_KLSModular_FunctionalInequalities_Analysis_Operator_Positive

open scoped RealInnerProductSpace
section General
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
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
