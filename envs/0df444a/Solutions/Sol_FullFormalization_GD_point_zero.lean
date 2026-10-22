-- Prove2me | solution 1 for FullFormalization.GD.point_zero
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:37:04.761376+00:00
-- url     : https://prove2.me/submissions/d8879bc0-caca-4002-82e0-d3a83e16d4e7

-- Generated from F:/20261008/FullFormalization\FullFormalization\GradientStrategies.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.GradientStrategies

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 21,
  strategies 1 and 2 (source lines 2079-2080):

      1. GD, step `1/L`;
      2. GD, step `1/(2L)`.

  Implementation semantics (source §19 authorises the frozen implementation,
  and §35's cross-check script imports it):
  `F:\Hardy_Run_2026-10-07_001215\workflow\hgcore\blackbox_algos.py`,
  `_gd_fixed_1_over_L` and `_gd_fixed_declared_steps`:

      point = _origin(spec)                      -- the origin
      for _ in range(spec.query_budget):         -- one query per step
          answer = oracle.query(point)
          point = point - size * answer["gradient"]
      oracle.finish(point)                       -- the final point is the output

  with `size = 1/L` for the first strategy and `size = 1/(2L)` for the second.
  Both start from the origin, so — as the implementation's own docstring says —
  the only difference between them is the step size.

  In the normalized coordinates of section 21 the starting point is `z = 0`,
  i.e. `x = x_init`; the two strategies below are written on the raw oracle and
  in normalized coordinates, which is the same thing since `z = 0` is the
  origin of `E`.

  Query bookkeeping: the loop body queries *then* steps, so the `N` queries are
  the iterates `p_0, ..., p_{N-1}` and the reported point is `p_N`.  There is no
  query at the output point (matching §5: no off-by-one, and matching source
  line 312-319 where `g_N` is a proof variable only for the NAG method).
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_GradientStrategies
import Definitions.Def_PortfolioDefinitions

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-! ### The shared fixed-step descent -/









/-! ### Strategy 1: gradient descent with step `1/L` -/

namespace GD

























end GD

/-! ### Strategy 2: gradient descent with step `1/(2L)` -/

namespace halfGD



























end halfGD

/-! ### The two strategies are a controlled comparison

Both start at the origin and differ only in the step size, exactly as the
frozen implementation's docstring says.  A half step is a step of the doubled
smoothness constant. -/







end FullFormalization

open FullFormalization
open FullFormalization.GD

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open FullFormalization.GD in
@[simp] theorem solution (o : Oracle E) (L : ℝ) : point o L 0 = 0 := rfl
