-- Prove2me | solution 1 for DSSYKScales.emergent_string_scale_integral
-- status  : ACCEPTED   (prove)
-- author  : @mrfancypants
-- created : 2026-09-28T23:40:11.218551+00:00
-- url     : https://prove2.me/submissions/060b6d6d-f3e5-49d2-aadb-7e08046e439d

import Mathlib
import Definitions.Def_DSSYKScales_defs

open Filter Topology

namespace DSSYKScales

theorem aux_esi_tanh_eq (x : ℝ) :
    Real.sinh x / Real.cosh x = (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x)) := by
  rw [Real.sinh_eq, Real.cosh_eq]
  have h1 : Real.exp (-2 * x) = Real.exp (-x) * Real.exp (-x) := by
    rw [← Real.exp_add]; ring_nf
  have h2 : Real.exp x * Real.exp (-x) = 1 := by
    rw [← Real.exp_add]; simp
  have hx : 0 < Real.exp x := Real.exp_pos x
  have hnx : 0 < Real.exp (-x) := Real.exp_pos (-x)
  rw [h1]
  field_simp
  nlinarith [h2]

theorem aux_esi_tendsto_top :
    Tendsto (fun x : ℝ => Real.sinh x / Real.cosh x) atTop (𝓝 1) := by
  simp_rw [aux_esi_tanh_eq]
  have h : Tendsto (fun x : ℝ => Real.exp (-2 * x)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => -2 * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by norm_num)
    exact Real.tendsto_exp_atBot.comp this
  have : Tendsto (fun x : ℝ => (1 - Real.exp (-2 * x)) / (1 + Real.exp (-2 * x))) atTop
      (𝓝 ((1 - 0) / (1 + 0))) :=
    ((tendsto_const_nhds (x := (1:ℝ))).sub h).div
      ((tendsto_const_nhds (x := (1:ℝ))).add h) (by norm_num)
  rwa [show ((1:ℝ) - 0) / (1 + 0) = 1 by norm_num] at this

theorem aux_esi_tendsto_bot :
    Tendsto (fun x : ℝ => Real.sinh x / Real.cosh x) atBot (𝓝 (-1)) := by
  have h := (aux_esi_tendsto_top.comp tendsto_neg_atBot_atTop).neg
  refine h.congr (fun x => ?_)
  simp [Function.comp, Real.sinh_neg, Real.cosh_neg, neg_div]

theorem aux_esi_deriv (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.sinh x / Real.cosh x) (1 / Real.cosh x ^ 2) x := by
  have hc : Real.cosh x ≠ 0 := (Real.cosh_pos x).ne'
  have := (Real.hasDerivAt_sinh x).div (Real.hasDerivAt_cosh x) hc
  have e : 1 / Real.cosh x ^ 2 =
      (Real.cosh x * Real.cosh x - Real.sinh x * Real.sinh x) / Real.cosh x ^ 2 := by
    rw [← sq, ← sq, Real.cosh_sq]; ring
  rw [e]
  exact this

theorem aux_esi_integrable :
    MeasureTheory.Integrable (fun x : ℝ => 1 / Real.cosh x ^ 2) := by
  refine integrable_inv_one_add_sq.mono' ?_ ?_
  · exact (Continuous.aestronglyMeasurable (by fun_prop (disch := exact fun x => by positivity)))
  · refine MeasureTheory.ae_of_all _ (fun x => ?_)
    have hc : 0 < Real.cosh x ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_pos (by positivity), one_div]
    apply inv_anti₀ (by positivity)
    rw [Real.cosh_sq']
    have : x ^ 2 ≤ Real.sinh x ^ 2 := by
      rcases le_total 0 x with h | h
      · have := Real.self_le_sinh_iff.2 h
        nlinarith
      · have := Real.sinh_le_self_iff.2 h
        nlinarith
    linarith

theorem aux_esi_base : ∫ t : ℝ, 1 / Real.cosh t ^ 2 = 2 := by
  rw [MeasureTheory.integral_of_hasDerivAt_of_tendsto aux_esi_deriv aux_esi_integrable
    aux_esi_tendsto_bot aux_esi_tendsto_top]
  norm_num

end DSSYKScales

open DSSYKScales

theorem solution (J q : ℝ) (hJ : 0 < J) (hq : 0 < q) :
    ∫ t : ℝ, 1 / Real.cosh (J * q * t) ^ 2 = 2 / (J * q) := by
  have hc : 0 < J * q := mul_pos hJ hq
  rw [MeasureTheory.Measure.integral_comp_mul_left (fun t => 1 / Real.cosh t ^ 2) (J * q),
    aux_esi_base, abs_of_pos (inv_pos.2 hc), smul_eq_mul]
  field_simp
