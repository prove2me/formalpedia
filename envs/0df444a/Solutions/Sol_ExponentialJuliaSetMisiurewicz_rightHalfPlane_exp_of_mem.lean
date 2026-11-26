-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.rightHalfPlane_exp_of_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:05:29.705144+00:00
-- url     : https://prove2.me/submissions/33df2924-cf77-4680-b96b-f6f1a56968ad

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_lemma2a_real_growth


set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ}
    (hs : z ∈ centralStrip) (hh : z ∈ rightHalfPlane) :
    Complex.exp z ∈ rightHalfPlane := by
  have h2a := lemma2a_real_growth hs
  have hlog : Real.log 2 < 1 := by
    have := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num)
    linarith
  have hre : (4 : ℝ) < z.re := hh
  show (4 : ℝ) < (Complex.exp z).re
  linarith
end ExponentialJuliaSetMisiurewicz
