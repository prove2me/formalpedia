-- Prove2me | solution 1 for AvramDividend.Classical.esscher_cumulative_origin_of_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T07:49:17.869142+00:00
-- url     : https://prove2.me/submissions/b6aaac25-e6cb-4da9-ab30-7333cf118fb1

import Theorems.Thm_AvramDividend_Classical_rightContinuous_cumulative_toReal_of_finite
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic.FunProp
import Mathlib.MeasureTheory.Measure.MeasureSpaceDef

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Set MeasureTheory Topology

theorem solution
    (β : Measure ℝ) (φ : ℝ) (W : ℝ → ℝ)
    (hβfin : ∀ x : ℝ, β (Set.Iic x) ≠ ⊤)
    (hW : ContinuousWithinAt W (Set.Ioi (0 : ℝ)) 0)
    (hEq : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x = (β (Set.Iic x)).toReal) :
    W 0 = (β (Set.Iic (0 : ℝ))).toReal := by
  have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici (0 : ℝ) := by
    intro x hx
    exact le_of_lt (Set.mem_Ioi.mp hx)
  have hβcont : ContinuousWithinAt
      (fun x : ℝ => (β (Set.Iic x)).toReal)
      (Set.Ioi (0 : ℝ)) 0 :=
    (AvramDividend.Classical.rightContinuous_cumulative_toReal_of_finite β hβfin 0).mono hsub
  have hβlim := hβcont.tendsto
  have hpoint : (fun x : ℝ => Real.exp (-(φ * x)) * W x) =ᶠ[
      nhdsWithin (0 : ℝ) (Set.Ioi 0)]
      (fun x : ℝ => (β (Set.Iic x)).toReal) := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hEq x hx
  have htilt : Tendsto (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0))
      (nhds ((β (Set.Iic (0 : ℝ))).toReal)) := by
    exact hβlim.congr' hpoint.symm
  have he : ContinuousAt (fun x : ℝ => Real.exp (-(φ * x))) 0 := by
    fun_prop
  have hc : ContinuousWithinAt
      (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (Set.Ioi (0 : ℝ)) 0 := he.continuousWithinAt.mul hW
  have hlim : Tendsto (fun x : ℝ => Real.exp (-(φ * x)) * W x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (W 0)) := by
    simpa using hc.tendsto
  exact tendsto_nhds_unique hlim htilt
