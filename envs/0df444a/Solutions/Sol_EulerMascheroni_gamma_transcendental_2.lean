-- Prove2me | solution 2 for EulerMascheroni.gamma_transcendental
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T13:21:39.697518+00:00
-- url     : https://prove2.me/submissions/c1e2054d-bdb9-4550-a10d-8d1f2a173b0a
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Mixed_hardy_identity
import Theorems.Thm_EulerMascheroni_Mixed_e_values_linear_independent
import Theorems.Thm_EulerMascheroni_Mixed_local_intersection_algebraicity_conjecture
set_option autoImplicit false

open EulerMascheroni.Mixed

theorem solution : Transcendental ℚ Real.eulerMascheroniConstant := by
  intro hgamma
  have hrel : (EulerMascheroni.gompertzConstant : ℂ) =
      (0 : ℂ) + (-Real.eulerMascheroniConstant : ℂ) * Complex.exp 1 +
      (1 : ℂ) * expEin 1 := by
    rw [expEin, hardy_identity]
    field_simp
    <;> ring
  have hdelta := local_intersection_algebraicity_conjecture 0 (-Real.eulerMascheroniConstant) 1
    isAlgebraic_zero hgamma.neg isAlgebraic_one (by simpa using hrel)
  have heq : (-EulerMascheroni.gompertzConstant : ℂ) +
      (-Real.eulerMascheroniConstant : ℂ) * Complex.exp 1 + (1 : ℂ) * expEin 1 = 0 := by
    linear_combination -hrel
  have hind := e_values_linear_independent (-EulerMascheroni.gompertzConstant)
    (-Real.eulerMascheroniConstant) 1 hdelta.neg hgamma.neg isAlgebraic_one
    (by simpa using heq)
  norm_num at hind
