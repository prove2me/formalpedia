-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_dampedRational_special_negative
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:54.871155+00:00
-- url     : https://prove2.me/submissions/bc66903d-63da-479c-869e-0303861a89a7

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Theorems.Thm_FourierJacobi_Analysis_tendsto_dampedRational
import Theorems.Thm_FourierJacobi_Algebra_finiteRegular_special_negative
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_lt_one
import Theorems.Thm_FourierJacobi_Algebra_inverseSqrt_pos
import Theorems.Thm_FourierJacobi_Analysis_paperE_eq_closedCore


set_option autoImplicit false
noncomputable section
open FourierJacobi FourierJacobi.Analysis
open FourierJacobi.Algebra Filter
open scoped Topology
set_option maxHeartbeats 4000000
namespace FourierJacobi.Analysis
theorem _root_.solution (q : ℝ) (hq : 1 < q) (a b : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1)
    (haM : a ≠ -1) (hbM : b ≠ -1) :
    Tendsto (fun T => ((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
      dampedRational (inverseSqrt q) a b (-(inverseSqrt q : ℂ)) T)
      (𝓝[Set.Ioo 0 1] 1)
      (𝓝 (((1 - (-1 : ℂ)) / ((q : ℂ) + 1)) *
        paperE q a b (-(inverseSqrt q : ℂ)))) := by
  rw [paperE_eq_closedCore q (by linarith)]
  have hA : 1 + a ≠ 0 := by intro he; apply haM; linear_combination he
  have hB : 1 + b ≠ 0 := by intro he; apply hbM; linear_combination he
  exact (tendsto_dampedRational (inverseSqrt q) a b (-(inverseSqrt q : ℂ))
    (finiteRegular_special_negative (inverseSqrt_pos hq) (inverseSqrt_lt_one hq)
      ha hb (sub_ne_zero.mpr ha₁) (sub_ne_zero.mpr hb₁)
      (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hab₁) hA hB)).const_mul _
end FourierJacobi.Analysis
