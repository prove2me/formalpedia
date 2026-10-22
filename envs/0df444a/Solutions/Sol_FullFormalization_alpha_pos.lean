-- Prove2me | solution 1 for FullFormalization.alpha_pos
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T06:04:40.110001+00:00
-- url     : https://prove2.me/submissions/10436619-6ab1-470a-a693-f493a8963594

-- Generated from F:/20261008/FullFormalization\FullFormalization\Positivity.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.Positivity

  Source sections 13-16: positivity of every weight in the certificate.

    * `h_pos`      — (13.1)
    * `H_pos`      — `H` is strictly increasing from `H_0 = 1`, by (5.1)
    * `D_pos`      — `D_j > 0` on the valid range
    * `a_pos`      — Lemma 13.1, first half
    * `b_pos`      — Lemma 13.1, second half; uses the identity
                     `b_j = H_j (j+3)/(4 D_j D_{j+1}) + h_j/D_j` derived from
                     (5.1) and (5.5), so positivity is immediate from `H, h, D > 0`
    * `alpha_pos`  — section 14
    * `betaT_eq`, `betaT_pos` — (15.1), (15.2), (15.3)
    * `beta_eq_P`, `beta_pos` — (16.2)-(16.4), via the source's substitution
                     `j = u + 1`, `N = u + v + 3`, `u, v >= 0`, and the explicit
                     polynomials `Pbeta (16.2)`, `Qbeta (16.3)` with all-positive
                     coefficients (`Pbeta_pos`, `Qbeta_pos`)

  None of these is a finite enumeration: the running index and `N` stay
  universally quantified throughout, and every statement is proved
  symbolically.
-/

import Mathlib
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_Positivity
import Theorems.Thm_FullFormalization_D_pos
import Theorems.Thm_FullFormalization_D_succ
import Theorems.Thm_FullFormalization_D_zero_capital
import Theorems.Thm_FullFormalization_H_pos_capital
import Theorems.Thm_FullFormalization_H_sub_H_pred
import Theorems.Thm_FullFormalization_H_zero
import Theorems.Thm_FullFormalization_a_eq
import Theorems.Thm_FullFormalization_a_last
import Theorems.Thm_FullFormalization_a_pos
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_h_pos

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace FullFormalization

/-! ### (13.1) `h_j > 0` -/





/-! ### `H_j > 0` -/





/-! ### `a_j > 0` and `b_j > 0`  (Lemma 13.1) -/









/-! ### Section 14: `alpha_j > 0` -/



/-! ### Section 15: `β_T > 0`  —  (15.1), (15.2), (15.3)

`β_T = ½ (a_{N-1} - (m_{N-1} + b_N)²)` by (6.5).  Evaluating the three pieces in
closed form — `a_{N-1} = N(N+7)/(N²+9N+6)`, `m_{N-1} = (N-1)/(N+2)`,
`b_N = 1 - a_{N-1}` — gives the rational function (15.1); the source then
substitutes `N = u + 2` to put the numerator in the all-positive form (15.2). -/







/-! ### Section 16: `β_j > 0`  —  (16.1)-(16.4)

Source (16.1) substitutes `j = u + 1`, `N = u + v + 3` with `u, v >= 0`, under
which `β_j` (6.3) becomes the ratio `P(u,v)/Q(u,v)` of the two polynomials
below; both have all coefficients of one sign, so `β_j > 0` is immediate.

The two coefficient lists are those of `scripts/gen_beta_data.py`, which
regenerates them exactly from the definitions of `a`, `b`, `h`, `H`, `D`, `m`,
`d` in `Coefficients.lean` (source (4.1)-(4.13)).  The source prints the
denominator factor `u² + 4uv + 2v² + 15u + 26v + 42`, which is `8 * D_{j+2}`
under the substitution; the factor `128 (u+4)² (u+v+4)(u+v+5)` likewise collects
the denominators `8 (N+1)(N+2)` of `H`, `2 (N+1)(N+2)` of `h` and `k + 3 = u+4`
of `m`.  Both `P` and `Q` are the sign-flipped (positive) versions: the raw
SymPy output carries an overall sign on each. -/













end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open FullFormalization in
theorem solution (N j : ℕ) (hN : 1 ≤ N) (hj : j + 1 ≤ N) : 0 < alpha N j := by
  simp only [alpha]
  exact div_pos (a_pos N (j + 1) hN hj) (by norm_num)
