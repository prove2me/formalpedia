-- Prove2me | solution 1 for FriedCrossing.FirstVariation.charpoly_roots
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:10:09.573546+00:00
-- url     : https://prove2.me/submissions/8b2ab095-4dba-4598-8ce1-dbe8ac21d4d3

import Definitions.Def_B1s_fried_crossing_rate_9_07
import Definitions.Def_B1s_fried_crossing_firstvariation_9_08
import Theorems.Thm_FriedCrossing_FirstVariation_trace_Nmat
import Theorems.Thm_FriedCrossing_FirstVariation_det_Nmat

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.FirstVariation
variable {K : Type*} [Field K]
namespace FriedCrossing.FirstVariation
theorem _root_.solution (Bcc Bcψ Bψc Bψψ p : K) (z : K) :
    z ^ 2 - (Nmat Bcc Bcψ Bψc Bψψ p).trace * z + (Nmat Bcc Bcψ Bψc Bψψ p).det = 0 ↔
      z = 0 ∨ z = Bcc * p / (Bcc * Bψψ - Bcψ * Bψc) := by
  rw [trace_Nmat, det_Nmat, add_zero]
  constructor
  · intro h
    have : z * (z - Bcc * p / (Bcc * Bψψ - Bcψ * Bψc)) = 0 := by rw [← h]; ring
    rcases mul_eq_zero.mp this with h0 | h0
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.mp h0)
  · rintro (rfl | rfl)
    · ring
    · ring
end FriedCrossing.FirstVariation
