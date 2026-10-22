-- Prove2me | solution 1 for FullFormalization.a_last
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T05:37:35.457989+00:00
-- url     : https://prove2.me/submissions/c5e647bd-1fe6-46bb-8658-69520455120a

-- Generated from F:/20261008/FullFormalization\FullFormalization\CoefficientIdentities.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.CoefficientIdentities

  Source: section 5, Lemma 5.1, of
  `auditable_full_proof_nag_and_five_algorithm_cn.md`.

    (5.1)  H_j - H_{j-1} = h_j
    (5.2)  H_{N-1} = d_N
    (5.3)  h_j = 1 + m_j h_{j+1}            (source index range j < N-1)
    (5.4)  h_{N-1} = 1 + m_{N-1}
    (5.5)  D_j - D_{j+1} = (j+3)/4          (j >= 1)
    (5.6)  D_{j+2} = D_{j+1} - 1 - m_j (D_j - D_{j+1})     (j >= 1)

  Every one of these is a *symbolic* identity in `N` and the running index.
  There is no finite enumeration and no numerical substitution anywhere: the
  index appears as a universally quantified natural number and the proofs are
  rational-function identities closed by `field_simp`/`ring`.

  Index convention.  Statements that in the source use `j - 1` are phrased
  here in a positive-index form (with `j = k + 1`) so that the Lean statement
  carries no truncated natural-number subtraction; the literal `j - 1` form is
  recorded as a corollary in each case, so that the transcription to the source
  stays checkable.

  Lemma 5.1 in the source states (5.3) only for `j < N-1`, but the underlying
  rational-function identity is unconditional; the source's `j = N-1` instance
  is (5.4).  The unconditional form is recorded, and the source's restricted
  form follows by specialisation.  This strengthens an *intermediate* lemma
  only; no source theorem statement is altered.

  Also recorded here are the two `a`-side relations that the telescoping
  certificate uses, (10.6) and its companion, which follow from (5.1) by
  clearing the denominators `D_j, D_{j+1}, D_{j+2}`.
-/

import Mathlib
import Definitions.Def_Coefficients

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace FullFormalization

/-! ### (5.1)  `H_j - H_{j-1} = h_j` -/





/-! ### (5.2)  `H_{N-1} = d_N` -/





/-! ### (5.3)  `h_j = 1 + m_j h_{j+1}` -/



/-! ### (5.4)  `h_{N-1} = 1 + m_{N-1}` -/







/-! ### (5.5)  `D_j - D_{j+1} = (j+3)/4` -/





/-! ### (5.6)  `D_{j+2} = D_{j+1} - 1 - m_j (D_j - D_{j+1})` -/



/-! ### The `a`-side relations of the telescoping certificate

Source (10.6): `a_{j-1} D_j = a_j D_{j+1} - h_j`; companion (used at (10.9)):
`a_{j+1} D_{j+2} = a_j D_{j+1} + h_{j+1}`. -/













end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

open FullFormalization in
theorem solution (N : ℕ) : a N N = 1 := by simp [a]
