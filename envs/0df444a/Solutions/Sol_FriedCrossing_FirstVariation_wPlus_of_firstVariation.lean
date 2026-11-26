-- Prove2me | solution 1 for FriedCrossing.FirstVariation.wPlus_of_firstVariation
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:10:42.803776+00:00
-- url     : https://prove2.me/submissions/8c6d03f7-ab9f-4355-9a9b-e5204529b216

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Theorems.Thm_FriedCrossing_FirstVariation_det_Nmat
import Theorems.Thm_FriedCrossing_TwinRate_wPlus_at_cddp


set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]
namespace FriedCrossing.FirstVariation
theorem _root_.solution {Bcc Bcψ Bψc Bψψ p : ℝ}
    (hr : 0 < (Nmat Bcc Bcψ Bψc Bψψ p).trace) :
    TwinRate.wPlus (Nmat Bcc Bcψ Bψc Bψψ p).trace (Nmat Bcc Bcψ Bψc Bψψ p).det =
      (Nmat Bcc Bcψ Bψc Bψψ p).trace := by
  rw [det_Nmat]; exact TwinRate.wPlus_at_cddp hr
end FriedCrossing.FirstVariation
