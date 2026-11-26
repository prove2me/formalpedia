-- Prove2me | solution 1 for FriedCrossing.FirstVariation.Bmat_mul_Nmat0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:56:35.022811+00:00
-- url     : https://prove2.me/submissions/e17452b7-80b2-4c43-bb12-9f32c396e383

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]
namespace FriedCrossing.FirstVariation
theorem _root_.solution (Bcc Bcψ Bψc Bψψ p : K) :
    Bmat Bcc Bcψ Bψc Bψψ * Nmat0 Bcc Bcψ p = (Bcc * Bψψ - Bcψ * Bψc) • Pmat p := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Bmat, Nmat0, Pmat, Matrix.mul_apply, Fin.sum_univ_two] <;> ring
end FriedCrossing.FirstVariation
