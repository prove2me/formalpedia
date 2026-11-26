-- Prove2me | solution 1 for FriedCrossing.FirstVariation.det_Bmat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:56:30.103839+00:00
-- url     : https://prove2.me/submissions/710c84ac-0cf9-4be9-8b0e-2241d16380d2

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]
namespace FriedCrossing.FirstVariation
theorem _root_.solution (Bcc Bcψ Bψc Bψψ : K) :
    (Bmat Bcc Bcψ Bψc Bψψ).det = Bcc * Bψψ - Bcψ * Bψc := by
  simp [Bmat, Matrix.det_fin_two]
end FriedCrossing.FirstVariation
