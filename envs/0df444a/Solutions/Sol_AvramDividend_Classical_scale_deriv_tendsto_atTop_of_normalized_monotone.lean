-- Prove2me | solution 1 for AvramDividend.Classical.scale_deriv_tendsto_atTop_of_normalized_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T18:18:39.260968+00:00
-- url     : https://prove2.me/submissions/8c1d1b9a-1855-4553-80b5-af8931a77ec7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth

open Filter AvramDividend.Classical
open scoped Topology ENNReal

theorem solution (W : ℝ → ℝ) (φ : ℝ)
    (hφ : 0 < φ) (hW1 : 0 < W 1)
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by
  have hd : ∀ x : ℝ, 0 < x → φ * W x ≤ deriv W x := by
    intro x hx
    exact normalized_derivative_lower_bound φ x htilt hx (hdiff x hx)
  obtain ⟨c, hc, hge⟩ :=
    normalized_eventual_derivative_growth
      φ 1 hφ (by norm_num) hW1 htilt hd
  have hlinear : Tendsto (fun x : ℝ => φ * x) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hφ).2 tendsto_id
  have hmodel :
      Tendsto (fun x : ℝ => c * Real.exp (φ * x)) atTop atTop :=
    (tendsto_const_mul_atTop_of_pos hc).2
      (Real.tendsto_exp_atTop.comp hlinear)
  exact tendsto_atTop_mono' atTop hge hmodel
