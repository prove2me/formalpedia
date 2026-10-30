-- Prove2me | solution 1 for DerivativeChainPrivate.cubic_graph_coordinate_parts
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:24:01.676512+00:00
-- url     : https://prove2.me/submissions/5f42b050-ae60-407c-a18e-a54fe6d9b881

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


theorem solution (β z e : ℂ) (α b : ℝ) (hz : z ≠ 0)
    (hβ : β/z = (α : ℂ)*z^2-(b : ℂ)+e/z) :
    β.re = z.re * (α*(z.re^2-3*z.im^2)-b)+e.re ∧
      β.im = z.im * (α*(3*z.re^2-z.im^2)-b)+e.im ∧
      (β/z).im = 2*α*z.re*z.im+(e/z).im := by
  have hgraph : β = (α : ℂ)*z^3-(b : ℂ)*z+e := by
    calc
      _ = ((α : ℂ)*z^2-(b : ℂ)+e/z)*z := (div_eq_iff hz).mp hβ
      _ = _ := by rw [add_mul,sub_mul,div_mul_cancel₀ _ hz]; ring
  refine ⟨?_,?_,?_⟩
  · rw [hgraph]
    simp only [pow_succ,pow_zero,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  · rw [hgraph]
    simp only [pow_succ,pow_zero,Complex.add_im,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  · rw [hβ]
    simp only [pow_two,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im]
    ring
