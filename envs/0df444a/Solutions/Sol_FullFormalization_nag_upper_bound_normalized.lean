-- Prove2me | solution 1 for FullFormalization.nag_upper_bound_normalized
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T07:27:04.213904+00:00
-- url     : https://prove2.me/submissions/e13fc236-98a3-4aba-b548-60d15afe4123

-- Generated from F:/20261008/FullFormalization\FullFormalization\TheoremA.lean (Phase 3-4): proof kept, declaration hoisted out
-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.TheoremA

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`.
  Theorem A (source lines 17-56, boxed at line 3002) assembled from the pieces
  that are already verified elsewhere in this development.

  The three layers:

  * `nag_upper_bound_normalized` — (1.1)/(17.1) in the normalised setting
    `L = 1`, `x⋆ = 0`, `f⋆ = 0`, where the initial point is `r` and the radius is
    `‖r‖`: `F_N - f⋆ = F_N ≤ τ_N ‖r‖²`.  For `N ≥ 2` this is the master
    certificate (7.1) of section 12 — `CertificateIdentities` (9.1), (10.1),
    (11.1), (11.2) fed into `MasterCertificate.telescope` — combined with the
    nonnegativity of the interpolation residual (2.2), of the square terms
    (sections 14-16) and of the weights (section 13).  For `N = 1` it is the
    dedicated certificate (18.1) of section 18 (`NAGUpperBound.boundary_bound`),
    whose value `1/6` is exactly `τ_1`, so the two branches join without gap.

  * `theorem_A_upper` — the general `L, R` form (19.1)/(32.1).  Given an
    admissible `f` with optimiser `x⋆` and `‖x₀ - x⋆‖ ≤ R`, the normalised
    function is `f_N y = (f (x⋆ + R y) - f⋆)/(L R²)`, which is
    `NormalizedAtZero`; `Scaling.gradient_scaled` and `Scaling.differentiable_scaled`
    (with the local `gradient_normalized`/`gradient_const_add`) show that both
    NAG trajectories are related by `x_k = x⋆ + R · x_k^N` (proved directly, as
    in `Scaling.nag_pair_scaled`, but starting from the general `x₀`), and
    `nag_upper_bound_normalized` applied to `f_N` then gives the bound.

  * `theorem_A_attainment` / `theorem_A` / `theorem_A_sup` — the equality case of
    section 20: the one-dimensional Huber function (`Huber1D.huber_attainment`)
    is `NormalizedAtZero` and attains `τ_N` exactly.  **The supremum claim is
    stated in both forms**: `theorem_A_sup` is the literal `sSup` statement, and
    `theorem_A` is the equivalent pair "every admissible function satisfies the
    upper bound" ∧ "some admissible function attains it".  The pair form is the
    one used to *prove* the supremum (upper half + attained value), and the two
    forms are equivalent, so neither weakens the mathematics.
    (`theorem_A_attainment_admissible` records the same attainment in the
    source's own `Admissible`-class vocabulary.)

  **Scalar-multiplication pitfall** (hit three times earlier in this project):
  a bare `(1/2) • v` elaborates the numeral at type `ℕ`.  Every scalar in this
  file is written with an explicit `ℝ` ascription, e.g. `((1 : ℝ) / 2) • v`.

  Nothing is postulated: no `sorry`, `admit`, `axiom` or `unsafe`.
-/

import Mathlib
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.InnerProductSpace.Dual
import Definitions.Def_Certificate
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_Huber1D
import Definitions.Def_NAGUpperBound
import Definitions.Def_Positivity
import Definitions.Def_RationalNAG
import Definitions.Def_Scaling
import Definitions.Def_TheoremA
import Theorems.Thm_FullFormalization_D_diff
import Theorems.Thm_FullFormalization_D_diff_prime
import Theorems.Thm_FullFormalization_D_ne_zero
import Theorems.Thm_FullFormalization_D_pos
import Theorems.Thm_FullFormalization_D_succ
import Theorems.Thm_FullFormalization_D_zero_capital
import Theorems.Thm_FullFormalization_H_last_eq_d
import Theorems.Thm_FullFormalization_H_last_eq_d_prime
import Theorems.Thm_FullFormalization_H_pos_capital
import Theorems.Thm_FullFormalization_H_sub_H_pred
import Theorems.Thm_FullFormalization_H_sub_H_pred_prime
import Theorems.Thm_FullFormalization_H_zero
import Theorems.Thm_FullFormalization_Ival_nonneg
import Theorems.Thm_FullFormalization_Pbeta_pos
import Theorems.Thm_FullFormalization_Qbeta_pos
import Theorems.Thm_FullFormalization_a_eq
import Theorems.Thm_FullFormalization_a_last
import Theorems.Thm_FullFormalization_a_pos
import Theorems.Thm_FullFormalization_alpha_pos
import Theorems.Thm_FullFormalization_b_eq
import Theorems.Thm_FullFormalization_b_last_eq
import Theorems.Thm_FullFormalization_b_pos
import Theorems.Thm_FullFormalization_b_zero
import Theorems.Thm_FullFormalization_betaT_eq
import Theorems.Thm_FullFormalization_betaT_num_shift
import Theorems.Thm_FullFormalization_betaT_pos
import Theorems.Thm_FullFormalization_beta_eq_P
import Theorems.Thm_FullFormalization_beta_pos
import Theorems.Thm_FullFormalization_boundary_N_eq_one
import Theorems.Thm_FullFormalization_boundary_bound
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_sub_pred
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_endpoint_identity
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner
import Theorems.Thm_FullFormalization_h_at_N
import Theorems.Thm_FullFormalization_h_last
import Theorems.Thm_FullFormalization_h_last_prime
import Theorems.Thm_FullFormalization_h_pos
import Theorems.Thm_FullFormalization_h_rec
import Theorems.Thm_FullFormalization_initial_identity
import Theorems.Thm_FullFormalization_interior_identity
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_succ_prime
import Theorems.Thm_FullFormalization_nagX_zero
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one
import Theorems.Thm_FullFormalization_nagY_zero
import Theorems.Thm_FullFormalization_tau_eq_inv
import Theorems.Thm_FullFormalization_tau_one
import Theorems.Thm_FullFormalization_telescope
import Theorems.Thm_FullFormalization_terminal_identity
import Theorems.Thm_FullFormalization_two_d_add_one

open scoped Gradient RealInnerProductSpace

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000

namespace FullFormalization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### (1.1) / (17.1): the upper bound in the normalised setting -/



/-! ### Auxiliary gradient lemmas for the scaling (32.1) -/











/-! ### (19.1): the general `L, R` upper bound -/



/-! ### (20.4): the matching lower bound, and Theorem A -/











end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedTactic false
set_option maxHeartbeats 2000000
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

open FullFormalization in

theorem solution {f : E → ℝ} (hf : NormalizedAtZero f) (r : E) (N : ℕ)
    (hN : 1 ≤ N) : f (nagX f 1 r N) - f 0 ≤ tau N * ‖r‖ ^ 2 := by
  rcases eq_or_lt_of_le hN with h1 | h2
  · -- `N = 1`: source section 18
    rw [← h1]
    calc f (nagX f 1 r 1) - f 0 ≤ ‖r‖ ^ 2 / 6 := boundary_bound hf r
      _ = tau 1 * ‖r‖ ^ 2 := by rw [tau_one]; ring
  · -- `N ≥ 2`: the master certificate (6.1)-(7.1)
    have hN2 : 2 ≤ N := h2
    let x : ℕ → E := fun k => nagX f 1 r k
    let y : ℕ → E := fun k => nagY f 1 r k
    let g : ℕ → E := fun k => ∇ f (nagX f 1 r k)
    let Fv : ℕ → ℝ := fun k => f (nagX f 1 r k)
    -- the algorithm relations (3.1)-(3.2), in the normalized form `L = 1`
    have hx0 : x 0 = r := nagX_zero f 1 r
    have hx1 : x 1 = r - g 0 := by
      simp only [x, g]
      rw [nagX_succ f 1 r 0, mom_zero, zero_smul, add_zero, nagY_succ_one, nagX_zero]
    have hy1 : y 1 = x 1 := by
      simp only [x, y]
      rw [nagX_succ f 1 r 0, mom_zero, zero_smul, add_zero]
    have hy2 : y 2 = x 1 - g 1 := by
      simp only [y, x, g]
      rw [nagY_succ_one f r 1]
    -- (8.3)-(8.5): the potential, `V_0 = 0`, `V_j = Vterm_j` for `1 ≤ j < N`
    -- and `V_N = VN`
    let Vt : ℕ → ℝ := fun j =>
      if j = 0 then 0 else if j = N then VN N r x g Fv else Vterm N r y g Fv j
    have hinit : Vt 1
        = -(a N 0 * (Istar (Fv 0) (x 0) (g 0)
            + Ival (Fv 0) (Fv 1) (x 0) (x 1) (g 0) (g 1)) + S0 N r x g) := by
      have hi := initial_identity N hN2 r x y g Fv hx0 hx1 hy1 hy2
      have hV : Vt 1 = V N r y g Fv 1 := by
        simp only [Vt]
        rw [if_neg (by norm_num : ¬ ((1 : ℕ) = 0)),
          if_neg (by omega : ¬ ((1 : ℕ) = N)),
          V, if_neg (by norm_num : ¬ ((1 : ℕ) = 0))]
      rw [hV]
      linarith
    -- (10.1) for `1 ≤ j ≤ N-2` and (11.1) for `j = N-1`
    have hstep : ∀ j, 1 ≤ j → j ≤ N - 1 →
        Vt (j + 1) - Vt j
          = -(b N j * Istar (Fv j) (x j) (g j)
              + a N j * Ival (Fv j) (Fv (j + 1)) (x j) (x (j + 1)) (g j) (g (j + 1))
              + Sterm N r y x g j) := by
      intro j hj1 hjN1
      by_cases hj2 : j + 2 ≤ N
      · -- interior: (10.1)
        have hxj : x j = y (j + 1) + g j := by
          simp only [x, y, g]
          rw [nagY_succ_one f r j]
          abel
        have hxj1 : x (j + 1) = (1 + mom j) • y (j + 1) - mom j • y j := nagX_succ_prime f 1 r j
        have hyj2 : y (j + 2) = x (j + 1) - g (j + 1) := nagY_succ_one f r (j + 1)
        have hid := interior_identity N j hj1 hj2 r x y g Fv hxj hxj1 hyj2
        have hVj : Vt j = Vterm N r y g Fv j := by
          simp only [Vt]
          rw [if_neg (by omega : ¬ (j = 0)), if_neg (by omega : ¬ (j = N))]
        have hVj1 : Vt (j + 1) = Vterm N r y g Fv (j + 1) := by
          simp only [Vt]
          rw [if_neg (by omega : ¬ ((j : ℕ) + 1 = 0)),
            if_neg (by omega : ¬ ((j : ℕ) + 1 = N))]
        have hSj : Sterm N r y x g j = Sj N y g j := by
          rw [Sterm, if_neg (by omega : ¬ (j = 0)), if_neg (by omega : ¬ (j = N - 1))]
        rw [hVj, hVj1, hSj]
        linarith
      · -- terminal: (11.1)
        have hjlast : j = N - 1 := by omega
        subst hjlast
        rw [show (N : ℕ) - 1 + 1 = N by omega]
        have hxN1 : x (N - 1) = (1 + mom (N - 2)) • y (N - 1) - mom (N - 2) • y (N - 2) := by
          have h := nagX_succ_prime f 1 r (N - 2)
          rw [show (N : ℕ) - 2 + 1 = N - 1 by omega] at h
          exact h
        have hyN : y N = (1 + mom (N - 2)) • y (N - 1) - mom (N - 2) • y (N - 2) - g (N - 1) := by
          have h := nagY_succ_one f r (N - 1)
          rw [show (N : ℕ) - 1 + 1 = N by omega] at h
          calc y N = x (N - 1) - g (N - 1) := h
            _ = (1 + mom (N - 2)) • y (N - 1) - mom (N - 2) • y (N - 2) - g (N - 1) := by
                  rw [hxN1]
        have hxN : x N = (1 + mom (N - 1)) • y N - mom (N - 1) • y (N - 1) := by
          have h := nagX_succ_prime f 1 r (N - 1)
          rw [show (N : ℕ) - 1 + 1 = N by omega] at h
          exact h
        have hte := terminal_identity N hN2 r x y g Fv hxN1 hyN hxN
        have hVj : Vt (N - 1) = V N r y g Fv (N - 1) := by
          simp only [Vt]
          rw [if_neg (by omega : ¬ (N - 1 = 0)), if_neg (by omega : ¬ (N - 1 = N)),
            V, if_neg (by omega : ¬ (N - 1 = 0))]
        have hVN : Vt N = VN N r x g Fv := by
          show (if N = 0 then 0 else if N = N then VN N r x g Fv
            else Vterm N r y g Fv N) = VN N r x g Fv
          rw [if_neg (by omega : ¬ (N = 0)), if_pos rfl]
        have hSj : Sterm N r y x g (N - 1) = Slast N y x g := by
          rw [Sterm, if_neg (by omega : ¬ (N - 1 = 0)), if_pos rfl]
        rw [hVj, hVN, hSj]
        linarith
    -- (11.2): the endpoint identity
    have hend : tau N * ‖r‖ ^ 2 - Fv N = -Vt N + b N N * Istar (Fv N) (x N) (g N) := by
      have he := endpoint_identity N (by omega : 1 ≤ N) r x g Fv
      have hVN : Vt N = VN N r x g Fv := by
        show (if N = 0 then 0 else if N = N then VN N r x g Fv
          else Vterm N r y g Fv N) = VN N r x g Fv
        rw [if_neg (by omega : ¬ (N = 0)), if_pos rfl]
      rw [hVN]
      linarith
    -- (7.1): telescoping
    have htel : tau N * ‖r‖ ^ 2 - Fv N
        = (∑ j ∈ Finset.range N,
            a N j * Ival (Fv j) (Fv (j + 1)) (x j) (x (j + 1)) (g j) (g (j + 1)))
          + (∑ j ∈ Finset.range (N + 1), b N j * Istar (Fv j) (x j) (g j))
          + (∑ j ∈ Finset.range N, Sterm N r y x g j) := by
      have h0 := telescope hN2 Vt (fun j => a N j) (fun j => b N j)
        (fun j => Ival (Fv j) (Fv (j + 1)) (x j) (x (j + 1)) (g j) (g (j + 1)))
        (fun j => Istar (Fv j) (x j) (g j))
        (fun j => Sterm N r y x g j) (tau N * ‖r‖ ^ 2) (Fv N) (b_zero N) hinit hstep hend
      exact h0
    -- (2.2): every `I_{j,j+1}` is nonnegative
    have hres1 : 0 ≤ ∑ j ∈ Finset.range N,
        a N j * Ival (Fv j) (Fv (j + 1)) (x j) (x (j + 1)) (g j) (g (j + 1)) := by
      apply Finset.sum_nonneg
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      exact mul_nonneg (le_of_lt (a_pos N j (by omega) (by omega)))
        (Ival_nonneg hf.convex hf.differentiable hf.smooth (x j) (x (j + 1)))
    -- (2.2) at the minimiser `x⋆ = 0`: every `I_{⋆,j}` is nonnegative
    have hres2 : 0 ≤ ∑ j ∈ Finset.range (N + 1), b N j * Istar (Fv j) (x j) (g j) := by
      apply Finset.sum_nonneg
      intro j hj
      have hjN : j ≤ N := by have := Finset.mem_range.mp hj; omega
      have hIs : 0 ≤ Istar (Fv j) (x j) (g j) := by
        have h0 := Ival_nonneg hf.convex hf.differentiable hf.smooth (0 : E) (x j)
        simpa [Istar, hf.value_at_zero, hf.grad_at_zero] using h0
      exact mul_nonneg (le_of_lt (b_pos N j (by omega) hjN)) hIs
    -- sections 14-16: every square term is nonnegative
    have hres3 : 0 ≤ ∑ j ∈ Finset.range N, Sterm N r y x g j := by
      apply Finset.sum_nonneg
      intro j hj
      have hjN : j < N := Finset.mem_range.mp hj
      rcases Nat.eq_zero_or_pos j with hj0 | hjpos
      · rw [hj0]
        have hD0 : 0 < D N 0 := D_pos N 0 (by omega) (by omega)
        have ha1 : 0 < a N 1 := a_pos N 1 (by omega) (by omega)
        rw [Sterm, if_pos rfl, S0]
        apply add_nonneg
        · exact mul_nonneg (by positivity) (sq_nonneg _)
        · exact mul_nonneg (by positivity) (sq_nonneg _)
      · by_cases hlast : j = N - 1
        · rw [hlast]
          have hbT : 0 < betaT N := betaT_pos N hN2
          rw [Sterm, if_neg (by omega : ¬ (N - 1 = 0)), if_pos rfl, Slast]
          apply add_nonneg
          · exact mul_nonneg (by norm_num) (sq_nonneg _)
          · exact mul_nonneg (le_of_lt hbT) (sq_nonneg _)
        · have hj1 : 1 ≤ j := hjpos
          have hjle : j ≤ N - 2 := by omega
          have hal : 0 < alpha N j := alpha_pos N j (by omega) (by omega)
          have hbe : 0 < beta N j := beta_pos N j hj1 hjle
          rw [Sterm, if_neg (by omega : ¬ (j = 0)), if_neg hlast, Sj]
          apply add_nonneg
          · exact mul_nonneg (le_of_lt hal) (sq_nonneg _)
          · exact mul_nonneg (le_of_lt hbe) (sq_nonneg _)
    -- conclude: `τ‖r‖² - F_N` is a sum of nonnegative terms
    have hfin : Fv N ≤ tau N * ‖r‖ ^ 2 := by linarith [htel, hres1, hres2, hres3]
    show Fv N - f 0 ≤ tau N * ‖r‖ ^ 2
    rw [hf.value_at_zero, sub_zero]
    exact hfin
