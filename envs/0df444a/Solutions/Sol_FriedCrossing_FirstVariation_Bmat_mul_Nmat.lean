-- Prove2me | solution 1 for FriedCrossing.FirstVariation.Bmat_mul_Nmat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:57:53.152629+00:00
-- url     : https://prove2.me/submissions/e59bce88-5eff-4ebe-b630-64352e2b2049

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Theorems.Thm_FriedCrossing_FirstVariation_Bmat_mul_Nmat0

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]
namespace FriedCrossing.FirstVariation
theorem _root_.solution {Bcc Bcψ Bψc Bψψ p : K} (h : Bcc * Bψψ - Bcψ * Bψc ≠ 0) :
    Bmat Bcc Bcψ Bψc Bψψ * Nmat Bcc Bcψ Bψc Bψψ p = Pmat p := by
  rw [Nmat, Matrix.mul_smul, Bmat_mul_Nmat0, smul_smul, one_div_mul_cancel h, one_smul]
end FriedCrossing.FirstVariation
