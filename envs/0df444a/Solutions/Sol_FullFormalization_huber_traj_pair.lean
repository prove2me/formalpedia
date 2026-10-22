-- Prove2me | solution 1 for FullFormalization.huber_traj_pair
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T06:27:06.431358+00:00
-- url     : https://prove2.me/submissions/845065cc-bec5-491c-b224-d9a0286f53db

-- Generated from F:/20261008/FullFormalization\FullFormalization\Huber1D.lean (Phase 3-4): proof kept, declaration hoisted out
import Mathlib
import Definitions.Def_Coefficients
import Definitions.Def_FunctionClass
import Definitions.Def_Huber1D
import Definitions.Def_RationalNAG
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_sub_pred
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_deriv_huber
import Theorems.Thm_FullFormalization_hasDerivAt_huber
import Theorems.Thm_FullFormalization_hasDerivAt_huber_pos
import Theorems.Thm_FullFormalization_hasDerivAt_linear
import Theorems.Thm_FullFormalization_hasDerivAt_neglinear
import Theorems.Thm_FullFormalization_hasDerivAt_sq_div_two
import Theorems.Thm_FullFormalization_huberC_le_traj
import Theorems.Thm_FullFormalization_huberC_mul
import Theorems.Thm_FullFormalization_huberC_pos
import Theorems.Thm_FullFormalization_huberClamp_of_abs_lt
import Theorems.Thm_FullFormalization_huberClamp_of_c_le
import Theorems.Thm_FullFormalization_huberClamp_of_le_neg
import Theorems.Thm_FullFormalization_huberE_succ
import Theorems.Thm_FullFormalization_huberE_zero
import Theorems.Thm_FullFormalization_huber_of_abs_le
import Theorems.Thm_FullFormalization_huber_of_c_le
import Theorems.Thm_FullFormalization_huber_of_le_neg
import Theorems.Thm_FullFormalization_huber_zero_fun
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_succ_prime
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false

namespace FullFormalization

/-! ## Section 20.0: the Huber function -/









/-! ## Elementary values of `huber`, `huberClamp` and the coefficients -/

































/-! ## Elementary derivatives of the two branches -/







/-! ## Section 20, lines 1853-1858: the analytic properties of `huber`

The derivative is computed by gluing the two branches at the two kinks `±c`;
the one-sided derivatives agree there (both are `±c`), so the gluing goes
through `HasDerivWithinAt.union`. -/

















/-! ## Source line 1857-1858: `0` is the unique minimizer -/






/-! ## Section 20.1-20.2: the NAG trajectory -/







/-! ## Section 20.3: the attained value (20.4) -/







/-! ## Theorem A, lower bound: the Huber function attains the bound -/



end FullFormalization

open FullFormalization

open scoped Gradient RealInnerProductSpace
open Set
set_option linter.unusedSectionVars false

open FullFormalization in

open FullFormalization in
@[simp] theorem nagX_zero (f : ℝ → ℝ) (L : ℝ) (x₀ : ℝ) : nagX f L x₀ 0 = x₀ := rfl

open FullFormalization in
@[simp] theorem nagY_zero (f : ℝ → ℝ) (L : ℝ) (x₀ : ℝ) : nagY f L x₀ 0 = x₀ := rfl

-- of its namespace as the top-level `theorem solution`, shorter
-- helpers pasted verbatim, imports rewritten to Def bundles and
-- Thm_ stubs.
/-
  FullFormalization.Huber1D

  Source: `auditable_full_proof_nag_and_five_algorithm_cn.md`, section 20
  (「定理 A 的 matching lower bound」, lines 1817-2046).

  The source fixes `L = 1`, `x⋆ = 0`, `x₀ = R > 0`, sets

      c = R / (2 d_N + 1)                                    (20.1)

  and defines the one-dimensional Huber function

      f x = x²/2            if |x| ≤ c
      f x = c |x| - c²/2    if |x| ≥ c                       (20.2)

  It then states (lines 1853-1858) that `f` is convex, differentiable, has a
  globally 1-Lipschitz gradient and has `0` as its unique minimizer, and proves
  the NAG trajectory identity

      x_j = R - d_j c                                        (20.3)

  together with the observation that the whole trajectory stays in the positive
  linear branch (`x_j ≥ c` for `j ≤ N`, source 20.2), whence

      (f(x_N) - f⋆) / R² = 2 / (N² + 7 N + 4)                (20.4)

  i.e. exactly `tau N` of `FullFormalization.Coefficients`.  This is the
  matching lower bound: the upper bound (19.1) is attained.

  ## Representation choices

  * The constant `c` is called `huberC` here: `d` is the coefficient sequence of
    `FullFormalization.Coefficients`, and `c` is used as a bound variable
    throughout the project, so a global `c` would be confusing.

  * `huber c : ℝ → ℝ` is stated for an arbitrary `c`; every property below
    carries the hypothesis `0 ≤ c` (or `0 < c`) that the source's `c`, being a
    quotient by the positive `2 d_N + 1`, always satisfies.

  * The gradient of `huber c` is the clipping `huberClamp c x = max (-c) (min c x)`
    of `x` to `[-c, c]`.  Its 1-Lipschitz property is `huberClamp_lipschitz`;
    it is monotone, which is how convexity of `huber c` is obtained (through
    `MonotoneOn.convexOn_of_deriv`).  Differentiability is proved by gluing the
    two branches at the kinks `±c`, where the one-sided derivatives agree.

  * **Index range of (20.3).**  The source writes `x_j = R - d_j c` for the
    iterates of the method.  The induction only ever queries `x_0, …, x_N`
    (the method stops at `x_N`), and it uses the branch hypothesis `x_j ≥ c`,
    which is *false* for `j > N`.  Accordingly `huber_traj` below is stated for
    `j ≤ N`, which is exactly the range on which (20.3) is true.  (For `N = 1`,
    `R = 1` one gets `c = 1/3`, `x_3 = -2/15` while `R - d_3 c = -1/4`: the
    unrestricted statement is false.)
-/

theorem solution (N : ℕ) {R : ℝ} (hR : 0 < R) :
    ∀ j, j ≤ N →
      nagX (huber (huberC N R)) 1 R j = R - d j * huberC N R ∧
      nagY (huber (huberC N R)) 1 R j = R - huberE j * huberC N R := by
  intro j
  induction j with
  | zero =>
      intro _
      exact ⟨by simp, by simp⟩
  | succ k ih =>
      intro hk
      have hkN : k ≤ N := Nat.le_of_succ_le hk
      obtain ⟨hX, hY⟩ := ih hkN
      have hc : 0 < huberC N R := huberC_pos hR
      have hcle : 0 ≤ huberC N R := hc.le
      -- the trajectory stays in the positive linear branch at step `k`
      have hlin : huberC N R ≤ R - d k * huberC N R := huberC_le_traj N k hR hkN
      -- the gradient step `y_{k+1} = x_k - ∇f(x_k)`
      have hYsucc : nagY (huber (huberC N R)) 1 R (k + 1) = R - (d k + 1) * huberC N R := by
        rw [nagY_succ_one, gradient_eq_deriv', deriv_huber hcle, hX,
          huberClamp_of_c_le hcle hlin]
        ring
      -- the momentum identity `m_k ((d_k + 1) - e_k) = d_{k+1} - d_k - 1`
      have hmom : mom k * ((d k + 1) - huberE k) = d (k + 1) - d k - 1 := by
        rcases Nat.eq_zero_or_pos k with hk0 | hkpos
        · subst hk0
          rw [huberE_zero, mom_zero]
          norm_num [d_one, d_zero]
        · have hd : (d k + 1) - (d (k - 1) + 1) = ((k : ℝ) + 3) / 4 := by
            rw [← d_sub_pred k hkpos]
            ring
          rw [huberE, if_neg (by omega), mom, hd, d_succ_sub k]
          have hk3 : ((k : ℝ) + 3) ≠ 0 := by positivity
          field_simp
          ring
      -- the extrapolation step (source 3.3)
      have hXsucc : nagX (huber (huberC N R)) 1 R (k + 1) = R - d (k + 1) * huberC N R := by
        rw [nagX_succ_prime, hYsucc, hY]
        simp only [smul_eq_mul]
        linear_combination (-huberC N R) * hmom
      exact ⟨hXsucc, by rw [huberE_succ]; exact hYsucc⟩
