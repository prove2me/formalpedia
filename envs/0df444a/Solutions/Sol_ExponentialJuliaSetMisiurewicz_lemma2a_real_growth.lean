-- Prove2me | solution 1 for ExponentialJuliaSetMisiurewicz.lemma2a_real_growth
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T03:59:37.136117+00:00
-- url     : https://prove2.me/submissions/421dc017-ac26-40f3-ae0d-369eab85650c

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Complex.OpenMapping
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Definitions.Def_ExpChaotic_Basic
import Definitions.Def_ExpChaotic_Expansion
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_succ
import Theorems.Thm_ExponentialJuliaSetMisiurewicz_expIterate_zero
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_succ
attribute [local simp] ExponentialJuliaSetMisiurewicz.expIterate_zero



set_option autoImplicit true
open Function Filter Set Metric
open scoped Topology NNReal Uniformity
open ExponentialJuliaSetMisiurewicz
noncomputable section
namespace ExponentialJuliaSetMisiurewicz
theorem _root_.solution {z : ℂ} (hz : z ∈ centralStrip) :
    z.re + (1 - Real.log 2) ≤ (Complex.exp z).re := by
  change |z.im| ≤ Real.pi / 3 at hz
  rw [Complex.exp_re]
  have him_nonneg : 0 ≤ |z.im| := abs_nonneg z.im
  have him_le_pi : |z.im| ≤ Real.pi := by
    have hpi : 0 ≤ Real.pi := le_of_lt Real.pi_pos
    nlinarith
  have hcos :
      (1 / 2 : ℝ) ≤ Real.cos z.im := by
    rw [← Real.cos_abs]
    have hthird_nonneg : 0 ≤ Real.pi / 3 := by
      positivity
    have hthird_le_pi : Real.pi / 3 ≤ Real.pi := by
      nlinarith [Real.pi_pos]
    have habs_mem :
        |z.im| ∈ Set.Icc (0 : ℝ) Real.pi := by
      constructor
      · exact abs_nonneg z.im
      · exact le_trans hz hthird_le_pi
    have hthird_mem :
        Real.pi / 3 ∈ Set.Icc (0 : ℝ) Real.pi := by
      exact ⟨hthird_nonneg, hthird_le_pi⟩
    have hanti :
        AntitoneOn Real.cos (Set.Icc (0 : ℝ) Real.pi) :=
      Real.strictAntiOn_cos.antitoneOn
    have hmono :
        Real.cos (Real.pi / 3) ≤ Real.cos |z.im| :=
      hanti habs_mem hthird_mem hz
    simpa [Real.cos_pi_div_three] using hmono
  have hexp :
      z.re + (1 - Real.log 2) ≤ Real.exp z.re / 2 := by
    have h :=
      Real.add_one_le_exp (z.re - Real.log 2)
    have hlog : Real.exp (Real.log 2) = 2 := by
      rw [Real.exp_log]
      norm_num
    rw [Real.exp_sub, hlog] at h
    nlinarith
  calc
    z.re + (1 - Real.log 2)
        ≤ Real.exp z.re / 2 := hexp
    _ ≤ Real.exp z.re * Real.cos z.im := by
          nlinarith [Real.exp_pos z.re]
end ExponentialJuliaSetMisiurewicz
