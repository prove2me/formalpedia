-- Prove2me | solution 1 for AvramDividend.Classical.vcstar_deriv_continuous_C1_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:14:49.177151+00:00
-- url     : https://prove2.me/submissions/32fec6eb-4ac7-4e5a-8d0a-cbdf6530cbf7

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

/-- C1 scale regularity and a positive normalising derivative imply
    continuity of the ordinary candidate derivative across the join. -/
theorem solution (W : ℝ → ℝ)
    (hcpos : 0 < (cstar W).toReal)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (hdpos : 0 < deriv W (cstar W).toReal) :
    ContinuousOn (deriv (vcstar W)) (Ioi (0 : ℝ)) := by
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
  let f : ℝ → ℝ := fun y => (Iic c).piecewise
    (fun z => deriv W z / deriv W c) (fun _ => 1) y
  have hleft : ContinuousOn (fun y => deriv W y / deriv W c) (Ioi (0 : ℝ)) :=
    (hreg.continuousOn_deriv_of_isOpen isOpen_Ioi le_rfl).div_const _
  have hright : ContinuousOn (fun _ : ℝ => (1 : ℝ)) (Ioi (0 : ℝ)) :=
    continuousOn_const
  have hbound : EqOn (fun y => deriv W y / deriv W c)
      (fun _ : ℝ => 1) (Ioi (0 : ℝ) ∩ frontier (Iic c)) := by
    intro y hy
    have hyc : y = c := by simpa [frontier_Iic] using hy.2
    subst y
    exact hratio
  have hpiece : ContinuousOn f (Ioi (0 : ℝ)) := by
    have hp := continuousOn_piecewise_ite hleft hright (by rfl) hbound
    simpa [f] using hp
  apply hpiece.congr
  intro x hx
  have hx0 : 0 < x := hx
  by_cases hxc : x < c
  · have hlocal : (vcstar W) =ᶠ[𝓝 x]
        (fun y : ℝ => W y / deriv W c) := by
      filter_upwards [eventually_lt_nhds hxc, eventually_gt_nhds hx0]
        with y hyc hy0
      simp [vcstar, barrierValue, c, not_lt.mpr hy0.le, hyc.le, hdiv]
    have hder : deriv (vcstar W) x = deriv W x / deriv W c := by
      rw [hlocal.deriv_eq]
      exact ((hdiff x hx0).hasDerivAt.div_const (deriv W c)).deriv
    simp [f, Set.piecewise, hxc.le, hder]
  · by_cases hcx : c < x
    · have hder := vcstar_deriv_eq_one_above_cstar W x hcx
      simp [f, Set.piecewise, not_le.mpr hcx, hder]
    · have heq : x = c := le_antisymm (le_of_not_gt hcx) (le_of_not_gt hxc)
      subst x
      have hfit : deriv (vcstar W) c = 1 :=
        vcstar_deriv_one_of_local_scale_deriv_positive
          W hc (hdiff c hc) hdpos
      have hf : f c = 1 := by
        simp [f, Set.piecewise, hratio]
      rw [hf]
      exact hfit
