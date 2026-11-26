-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.pi_le_abs_im_sub_of_exp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T04:10:11.418863+00:00
-- url     : https://prove2.me/submissions/b6088c27-81cb-41b7-b018-c36edbd61076

import Mathlib.Order.CompletePartialOrder
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Data.Nat.Nth
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Definitions.Def_ExpChaotic_Expansion
import Definitions.Def_ExpChaotic_StripGeometry
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_two_pi_le_abs_im_sub_of_exp_eq

set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {a b : ℂ}
    (h : Complex.exp a = Complex.exp b) (hne : a ≠ b) :
    Real.pi ≤ |a.im - b.im| := by
  have hsep := two_pi_le_abs_im_sub_of_exp_eq h hne
  linarith [Real.pi_pos]
end ExponentialJuliaSetMisiurewicz
