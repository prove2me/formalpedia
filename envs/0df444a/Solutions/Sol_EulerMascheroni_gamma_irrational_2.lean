-- Prove2me | solution 2 for EulerMascheroni.gamma_irrational
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-09-11T14:18:36.528582+00:00
-- url     : https://prove2.me/submissions/9d6b574b-9c70-4fa8-989e-e286fcab61f9
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_EulerMascheroni_gamma_transcendental
import Theorems.Thm_EulerMascheroni_gamma_irrational_of_transcendental

theorem solution : Irrational Real.eulerMascheroniConstant :=
  EulerMascheroni.gamma_irrational_of_transcendental EulerMascheroni.gamma_transcendental

#print axioms solution
