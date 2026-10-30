-- Prove2me | solution 1 for DerivativeChainPrivate.sixth_sextic_real_exterior
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T00:50:26.072838+00:00
-- url     : https://prove2.me/submissions/9627268d-1b39-4c5b-83bf-aeead0ce9163

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2400000
set_option maxRecDepth 16384
open Polynomial DerivativeChainPrivate MeasureTheory Set Filter
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped Topology BigOperators


theorem solution (x : ℝ) (hx : x ≤ -1/4 ∨ 3/2 ≤ x) :
    0 < x^2+(-85/43)*x+1445/1806+(24565/211302)/x := by
  rcases hx with hl | hr
  · have hx0 : x < 0 := by linarith
    have h3 : 0 ≤ (-1/4-x)^3 := pow_nonneg (by linarith) 3
    have h2 := sq_nonneg (x+1/4)
    have he : (x^2+(-85/43)*x+1445/1806+(24565/211302)/x)*x =
      x^3+(-85/43)*x^2+(1445/1806)*x+24565/211302 := by field_simp [ne_of_lt hx0] <;> ring
    nlinarith
  · have hx0 : 0 < x := by linarith
    have h3 : 0 ≤ (x-3/2)^3 := pow_nonneg (by linarith) 3
    have h2 := sq_nonneg (x-3/2)
    have he : (x^2+(-85/43)*x+1445/1806+(24565/211302)/x)*x =
      x^3+(-85/43)*x^2+(1445/1806)*x+24565/211302 := by field_simp [ne_of_gt hx0] <;> ring
    nlinarith
