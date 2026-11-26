-- Prove2me | solution 1 for FriedCrossing.FirstVariation.trace_Nmat_ne_zero_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:10:38.139821+00:00
-- url     : https://prove2.me/submissions/236ce039-f5d4-4950-a970-bcd66774f685

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
theorem _root_.solution {Bcc Bcψ Bψc Bψψ p : K} (hcc : Bcc ≠ 0)
    (hdet : Bcc * Bψψ - Bcψ * Bψc ≠ 0) :
    (Nmat Bcc Bcψ Bψc Bψψ p).trace ≠ 0 ↔ p ≠ 0 := by
  rw [trace_Nmat, Ne, div_eq_zero_iff, mul_eq_zero, not_or, not_or]
  constructor
  · intro h; exact h.1.2
  · intro hp; exact ⟨⟨hcc, hp⟩, hdet⟩
end FriedCrossing.FirstVariation
