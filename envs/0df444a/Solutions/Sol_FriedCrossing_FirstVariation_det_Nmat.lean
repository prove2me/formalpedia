-- Prove2me | solution 1 for FriedCrossing.FirstVariation.det_Nmat
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:39:30.776273+00:00
-- url     : https://prove2.me/submissions/02188af4-3cda-48fe-9f69-72cc3e0067a4

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]
namespace FriedCrossing.FirstVariation
theorem _root_.solution (Bcc Bcψ Bψc Bψψ p : K) : (Nmat Bcc Bcψ Bψc Bψψ p).det = 0 := by
  simp [Nmat, Nmat0, Matrix.det_fin_two]
end FriedCrossing.FirstVariation
