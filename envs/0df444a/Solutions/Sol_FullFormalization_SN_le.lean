-- Prove2me | solution 1 for FullFormalization.SN_le
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:37:32.507827+00:00
-- url     : https://prove2.me/submissions/c846eede-63a7-43ac-8be4-59eb040dbe6f

-- Generated from F:/20261008/FullFormalization\FullFormalization\PortfolioDefinitions.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.PortfolioDefinitions

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, sections 21 and
  30 (Theorem B, the five-algorithm portfolio).

  Section 21 fixes the objects this file defines:

    * the upstream task publishes `L > 0`, `R > 0` and `x_init`;
    * the function class is the differentiable convex globally `L`-smooth
      class of `FunctionClass.lean` (`Admissible`, with the unique-minimizer
      refinement `AdmissibleUnique`, source line 2065);
    * the five strategies run in the **normalized coordinate**

          z = (x - x_init) / R            (source line 2074),

      namely (1) GD with step `1/L`, (2) GD with step `1/(2L)`,
      (3) rational-NAG, (4) fixed-seed random search, (5) grid-then-refine;
    * the per-strategy loss is

          q_{A,N}(f) = (f(x_{out,A}) - f*) / (L R^2)     (source line 2090),

      and the portfolio value is

          S_N(f) = min_A q_{A,N}(f)                       (source line 2096).

  Representation choices:

  * `Oracle` is the query interface every strategy is written against: one
    oracle call returns a value *and* a gradient, exactly as the frozen
    implementation's `oracle.query(point)` returns `{"value": ..,
    "gradient": ..}` (`blackbox_algos.py`, `_gd_fixed_1_over_L` et al.).  The
    canonical instance for a differentiable function `f` is `oracleOf f`, whose
    gradient field is Mathlib's `∇ f` (`oracleOf_gradient`, defeq); the
    definitional equality is what makes `RationalNAG.nagX` — which is written
    against `∇ f` — literally the frozen Nesterov loop.

  * `toNormalized` / `ofNormalized` are the two directions of the change of
    variables (source line 2074).  `R ≠ 0` is needed for the round trips; the
    source has `R > 0` (line 2062).

  * `Strategy` is the five-element enumeration required by
    `DEPENDENCY_MAP.md` §36.4 ("`PortfolioDefinitions.Strategy` 为五元 `Fin 5`
    枚举，无 `∀` 量词"): five constructors, in the source's order 1-5.  There is
    no quantifier over algorithms anywhere in the portfolio; `SN` is the
    minimum over exactly these five.

  * `SN` takes the vector of the five per-strategy losses `Strategy → ℝ`.  The
    losses themselves are produced by the concrete runs of
    `GradientStrategies.lean`, `RandomSearch.lean` and `GridRefine.lean` (and
    `RationalNAG.lean` for strategy 3); `SNOf` packages that wiring, so
    `SNOf L R f fstar out` *is* the source's `S_N(f)` for the five outputs
    `out : Strategy → E`.
-/

import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_PortfolioDefinitions

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false

namespace FullFormalization

variable {E : Type*}

/-! ### The oracle -/



namespace Oracle







end Oracle

section OracleOf

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]







end OracleOf

/-! ### What a strategy run produces -/



/-! ### Normalized coordinates (source line 2074) -/

section Normalized

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]













end Normalized

/-! ### The loss of one strategy (source line 2090) -/

section Loss

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]







end Loss

/-! ### The five strategies and the portfolio minimum (source lines 2079-2096) -/















section Portfolio

variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]









end Portfolio

end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
variable {E : Type*}
section OracleOf
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
section Normalized
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
section Loss
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]

open FullFormalization in

theorem solution (q : Strategy → ℝ) (A : Strategy) : SN q ≤ q A := by
  cases A with
  | gd =>
      exact le_trans (min_le_left _ _)
        (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_left _ _)))
  | halfGD =>
      exact le_trans (min_le_left _ _)
        (le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (min_le_right _ _)))
  | nag =>
      exact le_trans (min_le_left _ _)
        (le_trans (min_le_left _ _) (min_le_right _ _))
  | rand => exact le_trans (min_le_left _ _) (min_le_right _ _)
  | grid => exact min_le_right _ _
