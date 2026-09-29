-- Prove2me | solution 1 for EulerMascheroni.exists_int_linear_forms_tendsto_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-12T19:45:03.423298+00:00
-- url     : https://prove2.me/submissions/e38d2286-5b44-4f10-a171-1e5f0914e6e4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_P2_foundation
import Theorems.Thm_EulerMascheroni_P2_f_saddle_limit
import Theorems.Thm_EulerMascheroni_P2_phase_compatible_primitive_saving
import Theorems.Thm_EulerMascheroni_P2_int_linear_forms_of_primitive_saving

theorem solution :
    ∃ p q : ℕ → ℤ, (∀ n, 0 < q n) ∧
      (∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0) ∧
      Filter.Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
        Filter.atTop (nhds 0) := by
  exact EulerMascheroni.P2.int_linear_forms_of_primitive_saving
    EulerMascheroni.P2.foundation.1
    EulerMascheroni.P2.f_saddle_limit
    EulerMascheroni.P2.phase_compatible_primitive_saving
