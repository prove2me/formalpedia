-- Prove2me | solution 1 for FullFormalization.theoremB_final
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T09:11:56.698235+00:00
-- url     : https://prove2.me/submissions/04888bd5-ee68-4580-8fae-f15e4798c2cf

-- Generated from F:/20261008/FullFormalization\FullFormalization\MainResults.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.MainResults

  Assembles the two headline results of the source document from the files that
  prove their halves, with **no hypothesis left standing in for a theorem**.

    * Theorem A — `auditable_full_proof_nag_and_five_algorithm_cn.md`, §17-§20:
      `TheoremA.theorem_A_upper`, `TheoremA.theorem_A_sup`;
    * Theorem B — §21-§32: `TheoremB.theoremB`, which up to now carried
      `TheoremAUpper N (GridSpace N)` as an explicit hypothesis because
      `TheoremA.lean` did not yet exist.

  This file supplies that hypothesis from `TheoremA.theorem_A_upper` and
  restates Theorem B without it.  Nothing is weakened: `TheoremAUpper` was
  always exactly the statement of Theorem A in the vocabulary of the portfolio
  file, and `TheoremB.theoremB`'s own docstring says so.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_CommonExtremizer
import Definitions.Def_FunctionClass
import Definitions.Def_GradientStrategies
import Definitions.Def_GridRefine
import Definitions.Def_HiddenDirection
import Definitions.Def_Huber1D
import Definitions.Def_LiftedHuber
import Definitions.Def_NAGUpperBound
import Definitions.Def_PortfolioDefinitions
import Definitions.Def_Positivity
import Definitions.Def_RandomSearch
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling
import Definitions.Def_TheoremA
import Definitions.Def_TheoremB
import Theorems.Thm_FullFormalization_theoremAUpper_of_theorem_A
import Theorems.Thm_FullFormalization_theoremB

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]







end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [FiniteDimensional ℝ E]

open FullFormalization in

theorem solution (N : ℕ) (hN : 1 ≤ N) (q : Fin N → GridSpace N)
    (L R : ℝ) (hL : 0 < L) (hR : 0 < R) (x_init : GridSpace N) :
    (∀ (f : GridSpace N → ℝ) (xstar : GridSpace N) (out : Strategy → GridSpace N),
        AdmissibleUnique L R f x_init xstar → out Strategy.nag = nagX f L x_init N →
        SNOf L R f (f xstar) out ≤ tau N) ∧
      (∃ u : GridSpace N, ‖u‖ = 1 ∧
        AdmissibleUnique L R (scaled L R x_init (liftedHuber u N)) x_init (x_init + R • u) ∧
        SNOf L R (scaled L R x_init (liftedHuber u N))
          ((scaled L R x_init (liftedHuber u N)) (x_init + R • u))
          (portfolioOutputScaled R x_init u q hN) = tau N) ∧
      tau N = 2 / ((N : ℝ) ^ 2 + 7 * (N : ℝ) + 4) :=
  theoremB N hN q (theoremAUpper_of_theorem_A N hN) L R hL hR x_init
