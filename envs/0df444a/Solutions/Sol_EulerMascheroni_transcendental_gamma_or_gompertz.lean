-- Prove2me | solution 1 for EulerMascheroni.transcendental_gamma_or_gompertz
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T13:22:53.812224+00:00
-- url     : https://prove2.me/submissions/74445890-03ad-4555-ab9b-4c2208d86dc6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_Mixed_hardy_identity
import Theorems.Thm_EulerMascheroni_Mixed_e_values_linear_independent
set_option autoImplicit false

open EulerMascheroni.Mixed

theorem solution :
    Transcendental ℚ Real.eulerMascheroniConstant ∨
      Transcendental ℚ EulerMascheroni.gompertzConstant := by
  by_cases hgamma : IsAlgebraic ℚ Real.eulerMascheroniConstant
  · right
    intro hdelta
    have hrel : (-EulerMascheroni.gompertzConstant : ℂ) +
        (-Real.eulerMascheroniConstant : ℂ) * Complex.exp 1 + (1 : ℂ) * expEin 1 = 0 := by
      rw [expEin, hardy_identity]
      field_simp
      <;> ring
    have hind := e_values_linear_independent (-EulerMascheroni.gompertzConstant)
      (-Real.eulerMascheroniConstant) 1 hdelta.neg hgamma.neg isAlgebraic_one
      (by simpa using hrel)
    norm_num at hind
  · exact Or.inl hgamma
