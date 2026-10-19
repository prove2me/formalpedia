-- Prove2me | solution 2 for CohnElkies.upperCosLaplaceKernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:10:13.19699+00:00
-- url     : https://prove2.me/submissions/5070ae5a-d679-44e2-8ab2-45e800f43d51

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators


theorem solution
    {c : ℝ} (hc : 0 < c) (T : ℝ) :
    IntegrableOn (upperCosLaplaceKernel c T) (Ioi 0) := by
  have hmeas : Measurable (upperCosLaplaceKernel c T) := by
    unfold upperCosLaplaceKernel; fun_prop
  refine Integrable.mono' (((exp_neg_integrableOn_Ioi 0 hc)).const_mul |T|)
    hmeas.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with a ha
  have ha' : (0:ℝ) < a := ha
  have hcos : 1 - Real.cos (a * T) ≤ |a * T| := by
    have h1 := Real.one_sub_sq_div_two_le_cos (x := a * T)
    have h2 := Real.neg_one_le_cos (a * T)
    have h3 : (a * T) ^ 2 = |a * T| ^ 2 := (sq_abs _).symm
    rcases le_total |a * T| 2 with h | h
    · nlinarith [abs_nonneg (a * T)]
    · linarith
  have hnn : 0 ≤ 1 - Real.cos (a * T) := by linarith [Real.cos_le_one (a * T)]
  have he := Real.exp_pos (-c * a)
  unfold upperCosLaplaceKernel
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), div_le_iff₀ ha']
  rw [abs_mul, abs_of_pos ha'] at hcos
  nlinarith

