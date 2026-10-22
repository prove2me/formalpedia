-- Prove2me | solution 1 for FullFormalization.terminal_identity
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T06:26:10.126316+00:00
-- url     : https://prove2.me/submissions/0dfdd289-9ea8-4560-98fc-904dee667502

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
import Theorems.Thm_FullFormalization_D_succ
import Theorems.Thm_FullFormalization_H_last_eq_d
import Theorems.Thm_FullFormalization_H_last_eq_d_prime
import Theorems.Thm_FullFormalization_H_sub_H_pred
import Theorems.Thm_FullFormalization_H_sub_H_pred_prime
import Theorems.Thm_FullFormalization_a_eq
import Theorems.Thm_FullFormalization_a_last
import Theorems.Thm_FullFormalization_b_eq
import Theorems.Thm_FullFormalization_h_at_N
import Theorems.Thm_FullFormalization_h_last
import Theorems.Thm_FullFormalization_h_last_prime
import Theorems.Thm_FullFormalization_h_rec

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
set_option linter.unusedSimpArgs false in
theorem solution (N : ℕ) (hN : 2 ≤ N) (r : E) (x y g : ℕ → E) (Fv : ℕ → ℝ)
    (hxN1 : x (N - 1) = (1 + mom (N - 2)) • y (N - 1) - mom (N - 2) • y (N - 2))
    (hyN : y N = (1 + mom (N - 2)) • y (N - 1) - mom (N - 2) • y (N - 2) - g (N - 1))
    (hxN : x N = (1 + mom (N - 1)) • y N - mom (N - 1) • y (N - 1)) :
    VN N r x g Fv - V N r y g Fv (N - 1)
      + b N (N - 1) * Istar (Fv (N - 1)) (x (N - 1)) (g (N - 1))
      + a N (N - 1) * Ival (Fv (N - 1)) (Fv N) (x (N - 1)) (x N) (g (N - 1)) (g N)
      + Slast N y x g = 0 := by
  rw [show V N r y g Fv (N - 1) = Vterm N r y g Fv (N - 1) from
    if_neg (by omega : (N - 1) ≠ 0)]
  simp only [Vterm, VN, Slast, betaT, quadForm, Ival, Istar, Q11, Q12, Q22]
  have hxNm1 : x (N - 1) = y N + g (N - 1) := by rw [hxN1, hyN]; abel
  rw [hxNm1, hxN]
  rw [show (N : ℕ) - 1 - 1 = N - 2 by omega,
      show (N : ℕ) - 1 + 1 = N by omega]
  have hc1 : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
    rw [Nat.cast_sub (show 1 ≤ N by omega)]; norm_num
  have hc2 : ((N - 2 : ℕ) : ℝ) = (N : ℝ) - 2 := by
    rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
  have hdN : d N = (N : ℝ) * ((N : ℝ) + 7) / 8 := rfl
  have hd1 : d (N - 1) = ((N : ℝ) - 1) * ((N : ℝ) + 6) / 8 := by
    simp only [d]; rw [hc1]; ring
  have hd2 : d (N - 2) = ((N : ℝ) - 2) * ((N : ℝ) + 5) / 8 := by
    simp only [d]; rw [hc2]; ring
  have hm1c : mom (N - 1) = ((N : ℝ) - 1) / ((N : ℝ) + 2) := by
    simp only [mom]; rw [hc1]; ring_nf
  have hDNN : D N N = ((N : ℝ) ^ 2 + 9 * (N : ℝ) + 6) / 8 := by
    rw [D_succ N N (by omega), hdN, hd1]; ring
  have hDm1 : D N (N - 1) = ((N : ℝ) ^ 2 + 11 * (N : ℝ) + 10) / 8 := by
    rw [D_succ N (N - 1) (by omega), show (N : ℕ) - 1 - 1 = N - 2 by omega, hdN, hd2]
    ring
  have hbN : b N N = 1 - a N (N - 1) := by rw [b_eq N N (by omega), a_last]
  have hbNm1 : b N (N - 1) = a N (N - 1) - a N (N - 2) := b_eq N (N - 1) (by omega)
  have hhNm1 : h N (N - 1) = 1 + mom (N - 1) := h_last_prime N (by omega)
  have ha1 : a N (N - 1) = d N / D N N := by
    rw [a_eq N (N - 1) (by omega), show (N : ℕ) - 1 + 1 = N by omega,
      H_last_eq_d_prime N (by omega)]
  have hH0 : H N (N - 2) = d N - 1 - mom (N - 1) := by
    have h := H_sub_H_pred_prime N (N - 1) (by omega)
    rw [show (N : ℕ) - 1 - 1 = N - 2 by omega] at h
    rw [h_last_prime N (by omega), H_last_eq_d_prime N (by omega)] at h
    linarith
  have ha0 : a N (N - 2) = (d N - 1 - mom (N - 1)) / D N (N - 1) := by
    rw [a_eq N (N - 2) (by omega), show (N : ℕ) - 2 + 1 = N - 1 by omega, hH0]
  rw [hbN, hbNm1, hhNm1, ha1, ha0, hDNN, hDm1, hdN, hm1c]
  simp only [zero_sub, sub_zero, neg_sub, inner_add_left, inner_add_right,
    inner_sub_left, inner_sub_right, inner_neg_left, inner_neg_right,
    inner_zero_left, inner_zero_right, real_inner_smul_left, real_inner_smul_right,
    norm_sub_sq_real, norm_add_sq_real, norm_smul, norm_neg, norm_zero,
    Real.norm_eq_abs, mul_pow, sq_abs,
    real_inner_self_eq_norm_sq (y (N - 1)), real_inner_self_eq_norm_sq (y N),
    real_inner_self_eq_norm_sq (g (N - 1)), real_inner_self_eq_norm_sq (g N),
    real_inner_comm (y N) (y (N - 1)), real_inner_comm (g N) (g (N - 1))]
  have hz1 : ((N : ℝ) ^ 2 + 9 * (N : ℝ) + 6) / 8 ≠ 0 := by positivity
  have hz2 : ((N : ℝ) ^ 2 + 11 * (N : ℝ) + 10) / 8 ≠ 0 := by positivity
  have hz3 : (N : ℝ) + 2 ≠ 0 := by positivity
  field_simp
  ring
