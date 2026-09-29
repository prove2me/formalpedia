-- Prove2me | solution 1 for FamousTheorems.luroth_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:11:32.687295+00:00
-- url     : https://prove2.me/submissions/28dfeb91-431f-4707-ac59-9d171fa62d9f

import Mathlib

theorem solution {K : Type*} [Field K] (E : IntermediateField K (RatFunc K)) :
    ∃ f : RatFunc K, E = IntermediateField.adjoin K {f} :=
  ⟨_, RatFunc.Luroth.eq_adjoin_generator⟩
