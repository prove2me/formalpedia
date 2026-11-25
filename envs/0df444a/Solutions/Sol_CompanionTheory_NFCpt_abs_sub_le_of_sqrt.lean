-- Prove2me | solution 1 for CompanionTheory.NFCpt.abs_sub_le_of_sqrt
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T06:59:33.751793+00:00
-- url     : https://prove2.me/submissions/14fbd522-ff4e-4156-b3d5-5df7c06384a7

import Mathlib
import Definitions.Def_CompanionTheory_AutomorphicTheory_DiscreteGroupWaves_IntegralEqOfSqrtCauchy

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open CompanionTheory CompanionTheory.NFCpt
open MeasureTheory Filter Topology
namespace CompanionTheory.NFCpt
theorem _root_.solution {a b d δ : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hd : 0 ≤ d) (hδ : 0 < δ)
    (h : |Real.sqrt a - Real.sqrt b| ≤ Real.sqrt d) : |a - b| ≤ d / δ + δ * (a + b) := by
  set x := Real.sqrt a
  set y := Real.sqrt b
  set z := Real.sqrt d
  have hx : a = x ^ 2 := (Real.sq_sqrt ha).symm
  have hy : b = y ^ 2 := (Real.sq_sqrt hb).symm
  have hz : d = z ^ 2 := (Real.sq_sqrt hd).symm
  have hx0 : 0 ≤ x := Real.sqrt_nonneg _
  have hy0 : 0 ≤ y := Real.sqrt_nonneg _
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have e : |a - b| = |x - y| * (x + y) := by
    rw [hx, hy, show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul, abs_of_nonneg (add_nonneg hx0 hy0)]
  rw [e, hx, hy, hz]
  have h1 : |x - y| * (x + y) ≤ z * (x + y) := mul_le_mul_of_nonneg_right h (add_nonneg hx0 hy0)
  refine h1.trans ?_
  rw [div_add' _ _ _ hδ.ne', le_div_iff₀ hδ]
  nlinarith [sq_nonneg (z - δ * x), sq_nonneg (z - δ * y), sq_nonneg (δ * x), sq_nonneg (δ * y), sq_nonneg z]
end CompanionTheory.NFCpt
