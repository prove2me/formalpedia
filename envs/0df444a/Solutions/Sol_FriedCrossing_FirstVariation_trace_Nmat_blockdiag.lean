-- Prove2me | solution 1 for FriedCrossing.FirstVariation.trace_Nmat_blockdiag
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:10:31.350844+00:00
-- url     : https://prove2.me/submissions/5c14ff54-4a93-40c8-94c9-acff6fea38ef

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Theorems.Thm_FriedCrossing_FirstVariation_trace_Nmat

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]
namespace FriedCrossing.FirstVariation
theorem _root_.solution {Bcc Bψψ p : K} (hcc : Bcc ≠ 0) (hψψ : Bψψ ≠ 0) :
    (Nmat Bcc 0 0 Bψψ p).trace = p / Bψψ := by
  rw [trace_Nmat]
  field_simp
  ring
end FriedCrossing.FirstVariation
