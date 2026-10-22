-- Prove2me | solution 1 for FullFormalization.initial_identity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T06:01:58.145982+00:00
-- url     : https://prove2.me/submissions/efac6355-9934-4edc-9ce4-d6d4d8a8e99a

-- Generated from F:/20261008/FullFormalization\FullFormalization\CertificateIdentities.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.CertificateIdentities

  Source sections 9-12: the local certificate identities and the master
  telescoping certificate.

  The identities are exact algebraic identities between quadratic forms in a
  few vectors and their function values.  They are *not* inequalities and no
  numerical testing is involved.  The relations that the source uses to
  eliminate the accumulated weights are stated abstractly, with free scalars:

    (10.6)  A = (B E - h)/D          (from  a_{j-1} D_j = a_j D_{j+1} - h_j)
    (10.7)  h_{j+1} = (h - 1)/m      (from  h_j = 1 + m_j h_{j+1})
    (10.8)  F = E - 1 - m (D - E)    (this is (5.6), the D recurrence)
    (10.9)  C = (B E + h_{j+1})/F    (from  a_{j+1} D_{j+2} = a_j D_{j+1} + h_{j+1})

  Proving the abstract form and then instantiating is exactly the source's own
  strategy (section 10.1 introduces the abstract parameters `D, E, F, h, m,
  A, B, C` and works with them); the instantiation uses `CoefficientIdentities`.

  Scalar names are `A B C Dd Ee Ff hh m` throughout this file, to avoid
  shadowing the ambient type variable `E`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Theorems.Thm_FullFormalization_D_ne_zero
import Theorems.Thm_FullFormalization_D_pos
import Theorems.Thm_FullFormalization_D_succ
import Theorems.Thm_FullFormalization_D_zero_capital
import Theorems.Thm_FullFormalization_H_sub_H_pred
import Theorems.Thm_FullFormalization_a_eq
import Theorems.Thm_FullFormalization_b_eq
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_tau_eq_inv
import Theorems.Thm_FullFormalization_two_d_add_one

open scoped Gradient RealInnerProductSpace
open Set

set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Abstract coefficient functions (source (8.1), (8.2), (6.3)-(6.4)) -/




















/-! ### Source (11.2): the endpoint identity

`τ‖r‖² - F_N = -V_N + b_N I_{⋆,N}`, equivalently `F_N - τ‖r‖² - V_N + b_N I_{⋆,N} = 0`.
This is a direct algebraic consequence of (8.5) and `b_N = 1 - a_{N-1}`
(source line 1264) — no geometry is involved. -/



/-! ### Source (11.1): the terminal identity

`V_N - V_{N-1} = -b_{N-1} I_{⋆,N-1} - a_{N-1} I_{N-1,N} - S_{N-1}`.

**Geometry.**  The source's prose labels the local vectors `p = y_{N-1}`,
`q = y_N`, but its formulas (11.3)-(11.4) are the Nesterov recurrences only
under the reading `y_{N-1}` for `q` and `y_{N-2}` for `p`; with that reading the
pair fed to `Q_{N-1}` is `(y_{N-1}, y_N)`, which is also what the source's own
cross-check script uses.  Concretely the source's (11.3)-(11.4) read

    x_{N-1} = (1 + m_{N-2}) y_{N-1} - m_{N-2} y_{N-2}
    y_N     = x_{N-1} - g_{N-1}
    x_N     = (1 + m_{N-1}) y_N - m_{N-1} y_{N-1}

which is exactly how the hypothesis set below is stated.  The identity is
confirmed by exact rational point evaluation for several `N` in
`scripts/verify_concrete_rigorous.py`.

**Proof.**  The geometry hypotheses eliminate `x_{N-1}`, `x_N` and `y_N`
(only `x_{N-1} = y_N + g_{N-1}` is used, so `m_{N-2}` and `y_{N-2}` disappear).
The coefficient identities of `CoefficientIdentities` then replace `b_N`,
`b_{N-1}`, `h_{N-1}`, `a_{N-1}`, `a_{N-2}`, `D_N`, `D_{N-1}` and `mom_{N-1}`
by closed forms; the remaining identity is a polynomial in `N` and in the six
vector atoms `‖y_{N-1}‖², ‖y_N‖², ⟪y_{N-1}, y_N⟫, ‖g_{N-1}‖², ‖g_N‖²,
⟪g_{N-1}, g_N⟫, …`, which `field_simp`/`ring` close.

The algebraic content is a single scalar relation between the terminal local
parameters.  Writing `a = a_{N-1}`, `m = m_{N-1}`, `P = D_N`, `Q = D_{N-1}`
the identity is equivalent to `P (a - m - 1) + Q m + 1 = 0`; this follows from
`D_N = d_N + (N+3)/4` and `D_{N-1} - D_N = (N+2)/4 = m (N+2)^2/4` with
`m (N+2) = N - 1`, since it collapses to `1 - (N+3)/4 + (N-1)/4 = 0`. -/



/-! ### Source (10.1): the interior identity, in concrete coefficients

`V_{j+1} - V_j = -b_j I_{j,j+1} - a_j I_{⋆,j} - S_j`, i.e. the same
decrement as the terminal identity but for `1 <= j <= N-2`.

**Geometry.**  The local data are `u = y_j`, `v = y_{j+1}`, `g_j`, `g_{j+1}`,
and the source's (10.2)-(10.4) read

    x_j     = y_{j+1} + g_j
    x_{j+1} = (1 + m_j) y_{j+1} - m_j y_j
    y_{j+2} = x_{j+1} - g_{j+1}

(the first being `y_{j+1} = x_j - g_j` rearranged).  Note that `hxj` is *not*
`x_j = y_j + g_j`: the interior decrement is measured between `V_j` and
`V_{j+1}`, so the point whose residual is `I_{⋆,j}` is `x_j`, and by (10.2)
that point equals `y_{j+1} + g_j`, not `y_j + g_j`.  Exact rational point
evaluation rejects the `y_j` reading, so the statement below uses `y (j+1)`.

This is the concrete instantiation of `interior_identity_abstract` (source
(10.1)) with `A = a_{j-1}, B = a_j, C = a_{j+1}, Dd = D_j, Ee = D_{j+1},
Ff = D_{j+2}, hh = h_j, m = m_j`; the `-τ‖r‖²` term cancels between the two
`Vterm`s, which is why only the difference appears.  The proof mirrors that of
`terminal_identity`: eliminate the geometry, replace every coefficient by its
closed form using `CoefficientIdentities`, normalise the inner products, and
close with `field_simp`/`ring`. -/



end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in
theorem solution (N : ℕ) (hN : 2 ≤ N) (r : E) (x y g : ℕ → E) (Fv : ℕ → ℝ)
    (hx0 : x 0 = r) (hx1 : x 1 = r - g 0) (hy1 : y 1 = x 1) (hy2 : y 2 = x 1 - g 1) :
    V N r y g Fv 1
        + a N 0 * (Istar (Fv 0) (x 0) (g 0)
            + Ival (Fv 0) (Fv 1) (x 0) (x 1) (g 0) (g 1))
        + S0 N r x g = 0 := by
  rw [show V N r y g Fv 1 = Vterm N r y g Fv 1 from if_neg (by norm_num : (1 : ℕ) ≠ 0)]
  simp only [Vterm, S0, quadForm, Ival, Istar, Q11, Q12, Q22]
  rw [show (1 : ℕ) - 1 = 0 by omega, show (1 : ℕ) + 1 = 2 by omega,
      hy1, hy2, hx0, hx1]
  rw [show a N 0 = H N 0 / D N 1 from a_eq N 0 (by omega),
      show a N 1 = H N 1 / D N 2 from a_eq N 1 (by omega),
      show b N 1 = a N 1 - a N 0 from b_eq N 1 (by omega)]
  rw [show a N 1 = H N 1 / D N 2 from a_eq N 1 (by omega),
      show a N 0 = H N 0 / D N 1 from a_eq N 0 (by omega)]
  have hH0 : H N 0 = 1 := by simp only [H]; norm_num
  rw [hH0, tau_eq_inv, D_zero_capital,
      show H N 1 = H N 0 + h N 1 from by
        have hh := H_sub_H_pred N 0
        linarith,
      hH0]
  have hh1 : h N 1 = 3 / 2 - 3 / (((N : ℝ) + 1) * ((N : ℝ) + 2)) := by
    have h1 : ((N : ℝ) + 1) ≠ 0 := by positivity
    have h2 : ((N : ℝ) + 2) ≠ 0 := by positivity
    simp only [h]
    push_cast
    field_simp
    ring
  rw [hh1]
  have hD1 : D N 1 ≠ 0 := D_ne_zero N 1 (by omega) (by omega)
  have hD2 : D N 2 ≠ 0 := D_ne_zero N 2 (by omega) (by omega)
  have hdpos : (0 : ℝ) < 2 * d N + 1 := by
    have := d_nonneg N
    linarith
  have hdne : 2 * d N + 1 ≠ 0 := ne_of_gt hdpos
  simp only [inner_add_left, inner_add_right, inner_sub_left, inner_sub_right,
    inner_neg_left, inner_neg_right, inner_zero_left, inner_zero_right,
    real_inner_smul_left, real_inner_smul_right,
    norm_sub_sq_real, norm_add_sq_real, norm_smul, norm_neg, norm_zero,
    Real.norm_eq_abs, mul_pow, sq_abs, zero_sub, sub_zero, zero_pow (by norm_num : 2 ≠ 0),
    real_inner_self_eq_norm_sq,
    real_inner_comm r (g 0), real_inner_comm r (g 1), real_inner_comm (g 0) (g 1)]
  field_simp
  rw [D_succ N 1 (by omega), D_succ N 2 (by omega),
      show 1 - 1 = 0 by omega, show 2 - 1 = 1 by omega, d_zero, d_one]
  simp only [d]
  push_cast
  ring
