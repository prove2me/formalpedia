-- Prove2me | solution 1 for EulerMascheroni.gamma_irrational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @Lucas
-- created : 2026-09-10T21:24:24.168416+00:00
-- url     : https://prove2.me/submissions/6a7b2916-8fc8-47ec-8723-e1b3e015d6c0
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_gamma_irrational_of_linear_forms
import Theorems.Thm_EulerMascheroni_exists_int_linear_forms_tendsto_zero

open Real

theorem solution : Irrational Real.eulerMascheroniConstant := by
  obtain ⟨p, q, -, hne, hlim⟩ := EulerMascheroni.exists_int_linear_forms_tendsto_zero
  exact EulerMascheroni.gamma_irrational_of_linear_forms p q hne hlim
