-- Prove2me | solution 1 for FirstPassageLinearTransport.tendsto_polylogTerminalRank_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:57:59.182238+00:00
-- url     : https://prove2.me/submissions/2905f461-25d0-4def-a87f-ce7fdfbf0eea

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Definitions.Def_FirstPassageLinearTransport_PolylogTerminalSchedule
import Theorems.Thm_FirstPassageLinearTransport_polylogTerminalRank_lower

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {A : ℝ} (hA : 0 < A) :
    Tendsto (polylogTerminalRank A) atTop atTop := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop (2 : ℝ)
      tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 2))
      atTop atTop := Real.tendsto_log_atTop.comp hxT
  have hcoef : 0 < A / Real.log 2 :=
    div_pos hA (Real.log_pos (by norm_num))
  have hreal : Tendsto
      (fun M : ℕ => A * Real.logb 2 ((M : ℝ) + 2)) atTop atTop := by
    have hmul := hlogT.const_mul_atTop hcoef
    simpa [Real.logb, div_eq_mul_inv, mul_assoc, mul_left_comm,
      mul_comm] using hmul
  rw [tendsto_atTop]
  intro N
  have hN := (tendsto_atTop.1 hreal) (N : ℝ)
  filter_upwards [hN] with M hN
  have hceil := polylogTerminalRank_lower A M
  have hcast : (N : ℝ) ≤ (polylogTerminalRank A M : ℝ) :=
    hN.trans hceil
  exact_mod_cast hcast
end FirstPassageLinearTransport
