-- Prove2me | solution 1 for FriedCrossing.FirstVariation.trace_Nmat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:39:41.763653+00:00
-- url     : https://prove2.me/submissions/36089aa3-5568-4b2d-bcde-aecde542e453

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
    (Nmat Bcc Bcψ Bψc Bψψ p).trace = Bcc * p / (Bcc * Bψψ - Bcψ * Bψc) := by
  have : (Nmat Bcc Bcψ Bψc Bψψ p).trace =
      1 / (Bcc * Bψψ - Bcψ * Bψc) * 0 + 1 / (Bcc * Bψψ - Bcψ * Bψc) * (Bcc * p) := by
    simp [Nmat, Nmat0, Matrix.trace_fin_two]
  rw [this]; ring
end FriedCrossing.FirstVariation
