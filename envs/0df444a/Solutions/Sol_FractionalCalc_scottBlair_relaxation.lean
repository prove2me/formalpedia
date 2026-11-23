-- Prove2me | solution 1 for FractionalCalc.scottBlair_relaxation
-- status  : ACCEPTED   (prove)
-- author  : @Xeroth
-- created : 2026-11-23T16:57:43.244807+00:00
-- url     : https://prove2.me/submissions/d5297954-16c2-461a-88af-9d3b36f78d5f

import Mathlib
import Definitions.Def_FractionalCalc_scottBlair
open MeasureTheory Set Classical

namespace FractionalCalc
lemma rlI_step (α x : ℝ) (hα0 : 0 < α) (hα1 : α < 1) (hx : 0 < x) :
    rlIntegral 0 (1 - α) heaviside x = x ^ (1 - α) / ((1 - α) * Real.Gamma (1 - α)) := by
  have hne : (1 - α) ≠ 0 := by linarith
  unfold rlIntegral
  rw [if_neg hne]
  have h1 : ∫ t in Ioo 0 x, (x - t) ^ (1 - α - 1) * heaviside t
      = ∫ t in (0:ℝ)..x, (x - t) ^ (-α) := by
    rw [intervalIntegral.integral_of_le hx.le, ← integral_Ioc_eq_integral_Ioo]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    simp only [heaviside, if_pos ht.1]
    rw [mul_one]; congr 1; ring
  rw [h1, intervalIntegral.integral_comp_sub_left (fun t => t ^ (-α)) x]
  rw [integral_rpow (Or.inl (by linarith))]
  simp only [sub_zero, sub_self]
  rw [Real.zero_rpow (by linarith)]
  have : -α + 1 = 1 - α := by ring
  rw [this]
  field_simp
  simp

end FractionalCalc

open FractionalCalc in
theorem solution (E τ α : ℝ) (t : ℝ)
    (hE : 0 < E) (hτ : 0 < τ) (hα0 : 0 < α) (hα1 : α < 1) (ht : 0 < t) :
    scottBlairRelaxation E τ α t = E * τ ^ α * t ^ (-α) / Real.Gamma (1 - α) := by
  unfold scottBlairRelaxation rlDeriv
  have hfl : Nat.floor α = 0 := Nat.floor_eq_zero.mpr hα1
  simp only [hfl, zero_add, Nat.cast_one]
  rw [iteratedDeriv_one]
  have heq : rlIntegral 0 (1 - α) heaviside =ᶠ[nhds t]
      fun x => x ^ (1 - α) / ((1 - α) * Real.Gamma (1 - α)) := by
    filter_upwards [Ioi_mem_nhds ht] with x hx
    exact rlI_step α x hα0 hα1 hx
  rw [heq.deriv_eq]
  have hd : HasDerivAt (fun x : ℝ => x ^ (1 - α) / ((1 - α) * Real.Gamma (1 - α)))
      ((1 - α) * t ^ (1 - α - 1) / ((1 - α) * Real.Gamma (1 - α))) t :=
    (Real.hasDerivAt_rpow_const (Or.inl ht.ne')).div_const _
  rw [hd.deriv]
  have hne : (1 - α) ≠ 0 := by linarith
  have : 1 - α - 1 = -α := by ring
  rw [this]
  field_simp
