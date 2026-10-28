-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_piecewise_ratio_one_of_C1_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T08:13:41.497979+00:00
-- url     : https://prove2.me/submissions/30a6e4b5-1da1-43dc-9e92-6a3fbfe82b0d

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.Piecewise
import Mathlib.Topology.Order.DenselyOrdered
import Mathlib.Topology.Order.OrderClosed
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_local_scale_deriv_positive
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_eq_one_above_cstar

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Filter Set Topology
open scoped NNReal ENNReal

/-- The exact ordinary derivative of the positive optimal-barrier profile. -/
theorem solution (W : ℝ → ℝ)
    (hcpos : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (hdpos : 0 < deriv W (cstar W).toReal) :
    ∀ x : ℝ, 0 < x →
      deriv (vcstar W) x =
        (Iic (cstar W).toReal).piecewise
          (fun y : ℝ => deriv W y / deriv W (cstar W).toReal)
          (fun _ : ℝ => (1 : ℝ)) x := by
  let c : ℝ := (cstar W).toReal
  have hc : 0 < c := hcpos
  have hcne : c ≠ 0 := ne_of_gt hc
  have hscale : scaleDeriv W c = ((deriv W c : ℝ) : EReal) := by
    simp [scaleDeriv, hcne]
  have hdiv (y : ℝ) :
      divE (W y) (scaleDeriv W c) = W y / deriv W c := by
    simp [hscale, divE]
  have hratio : deriv W c / deriv W c = 1 :=
    div_self (ne_of_gt hdpos)
  have hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x := by
    intro x hx
    exact (hreg.differentiableOn_one x hx).differentiableAt
      (Ioi_mem_nhds hx)
  intro x hx
  by_cases hxc : x < c
  · have hlocal : (vcstar W) =ᶠ[𝓝 x]
        (fun y : ℝ => W y / deriv W c) := by
      filter_upwards [eventually_lt_nhds hxc, eventually_gt_nhds hx]
        with y hyc hy0
      simp [vcstar, barrierValue, c, not_lt.mpr hy0.le, hyc.le, hdiv]
    have hder : deriv (vcstar W) x = deriv W x / deriv W c := by
      rw [hlocal.deriv_eq]
      exact ((hdiff x hx).hasDerivAt.div_const (deriv W c)).deriv
    simp [Set.piecewise, c, hxc.le, hder]
  · by_cases hcx : c < x
    · have hder := vcstar_deriv_eq_one_above_cstar W x hcx
      simp [Set.piecewise, c, not_le.mpr hcx, hder]
    · have heq : x = c :=
        le_antisymm (le_of_not_gt hcx) (le_of_not_gt hxc)
      subst x
      have hfit : deriv (vcstar W) c = 1 :=
        vcstar_deriv_one_of_local_scale_deriv_positive
          W hc (hdiff c hc) hdpos
      simp [Set.piecewise, c, hratio, hfit]
