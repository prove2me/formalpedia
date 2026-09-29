-- Prove2me | solution 1 for EulerMascheroni.irrational_gamma_or_gompertz
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:18:37.294358+00:00
-- url     : https://prove2.me/submissions/29d0b733-0fbf-4399-81ae-bd2d8efb17f4
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_transcendental_gamma_or_gompertz

theorem solution :
    Irrational Real.eulerMascheroniConstant ∨ Irrational EulerMascheroni.gompertzConstant := by
  rcases EulerMascheroni.transcendental_gamma_or_gompertz with h | h
  · exact Or.inl h.irrational
  · exact Or.inr h.irrational

#print axioms solution
