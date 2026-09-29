-- Prove2me | solution 2 for EulerMascheroni.exists_int_linear_forms_tendsto_zero
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-25T22:46:04.963964+00:00
-- url     : https://prove2.me/submissions/3268bc4e-9f7c-4305-bfa4-799d0f9e9703
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_EulerMascheroni_gamma_transcendental
import Theorems.Thm_EulerMascheroni_gamma_irrational_of_transcendental
import Theorems.Thm_Irrational_exists_int_linear_forms_tendsto_zero

open Real

theorem solution :
    ∃ p q : ℕ → ℤ, (∀ n, 0 < q n) ∧
      (∀ n, (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ) ≠ 0) ∧
      Filter.Tendsto (fun n => (q n : ℝ) * Real.eulerMascheroniConstant - (p n : ℝ))
        Filter.atTop (nhds 0) :=
  Irrational.exists_int_linear_forms_tendsto_zero
    (EulerMascheroni.gamma_irrational_of_transcendental EulerMascheroni.gamma_transcendental)
