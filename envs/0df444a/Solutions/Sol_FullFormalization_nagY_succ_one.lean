-- Prove2me | solution 1 for FullFormalization.nagY_succ_one
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:53:51.770702+00:00
-- url     : https://prove2.me/submissions/300caa07-0216-4119-b27d-653067901239

-- Generated from F:/20261008/FullFormalization\FullFormalization\RationalNAG.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.RationalNAG

  The rational-momentum Nesterov method, source section 3.

  Source lines 27-45 and 285-310:

      y_0 = x_0
      y_{k+1} = x_k - (1/L) ∇f(x_k)
      x_{k+1} = y_{k+1} + m_k (y_{k+1} - y_k),   m_k = k/(k+3),   k = 0, ..., N-1

  and the reported output is the **final extrapolated point `x_N`**
  (source line 46, emphasised).  This module defines exactly that two-sequence
  method and records the three relations (3.1), (3.2), (3.3) verbatim.

  There is no off-by-one shift anywhere: `nagX f L x₀ k` is `x_k` and
  `nagY f L x₀ k` is `y_k`, both indexed from `0`, and `nagPair … 0 = (x₀, x₀)`
  encodes `y_0 = x_0`.

  The proof variable `g_N = ∇f(x_N)` of source lines 312-319 is *not* part of
  this definition: the algorithm performs no gradient query at its output
  point.  `g_N` appears only inside `Certificate.lean`, as a free variable.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_RationalNAG
import Theorems.Thm_FullFormalization_nagY_succ

namespace FullFormalization

open scoped Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

























end FullFormalization

open FullFormalization

open scoped Gradient
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in

theorem solution (f : E → ℝ) (x₀ : E) (k : ℕ) :
    nagY f 1 x₀ (k + 1) = nagX f 1 x₀ k - ∇ f (nagX f 1 x₀ k) := by
  rw [nagY_succ]
  norm_num
