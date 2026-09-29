-- Prove2me | solution 1 for DiracEquation.gammaDirac_isGammaFamily
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T09:17:22.475667+00:00
-- url     : https://prove2.me/submissions/a47ea0d1-919f-42fd-9357-9f4a7ab10f92

import Definitions.Def_DiracEquation_fields

open DiracEquation

namespace Ag1Aux_DiracGamma

set_option maxHeartbeats 3000000 in
theorem gamma_family : IsGammaFamily gammaDirac := by
  intro mu nu
  fin_cases mu <;> fin_cases nu <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [gammaDirac, eta, Matrix.mul_apply, Fin.sum_univ_four, Matrix.one_apply] <;> ring_nf <;>
    simp

end Ag1Aux_DiracGamma

open Ag1Aux_DiracGamma

theorem solution : IsGammaFamily gammaDirac := gamma_family
