-- Prove2me | solution 1 for FourierJacobi.Analysis.tendsto_dampedRational_principal
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:49:09.654412+00:00
-- url     : https://prove2.me/submissions/8a90f827-95b8-4d5c-a2a4-1bc738fc930a

import Definitions.Def_FourierJacobi_Analysis_CoreParameters
import Mathlib.Tactic.FunProp
import Definitions.Def_FourierJacobi_Analysis_RationalLimits
import Theorems.Thm_FourierJacobi_Analysis_tendsto_dampedRational
import Theorems.Thm_FourierJacobi_Algebra_finiteRegular_unitary
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
theorem _root_.solution (q : ℝ) (hq : 1 < q) (a b d : ℂ)
    (ha : ‖a‖ = 1) (hb : ‖b‖ = 1) (hd : ‖d‖ = 1)
    (ha₁ : a ≠ 1) (hb₁ : b ≠ 1) (hab : a ≠ b) (hab₁ : a * b ≠ 1) :
    Tendsto (fun T => 2 / ((q : ℂ) + 1) * dampedRational (inverseSqrt q) a b d T)
      (𝓝[Set.Ioo 0 1] 1) (𝓝 (2 / ((q : ℂ) + 1) * paperE q a b d)) := by
  rw [paperE_eq_closedCore q (by linarith)]
  exact (tendsto_dampedRational (inverseSqrt q) a b d
    (finiteRegular_unitary (inverseSqrt_pos hq).le (inverseSqrt_lt_one hq)
      ha hb hd (sub_ne_zero.mpr ha₁) (sub_ne_zero.mpr hb₁)
      (sub_ne_zero.mpr hab) (sub_ne_zero.mpr hab₁))).const_mul _
end FourierJacobi.Analysis
