-- Prove2me | solution 1 for FullFormalization.theorem_A_upper
-- status  : ACCEPTED   (prove)
-- author  : @Somehow
-- created : 2026-10-09T07:37:31.807567+00:00
-- url     : https://prove2.me/submissions/ae986bd3-aede-48e1-a047-2fe8236c23df

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
import Theorems.Thm_FullFormalization_comp_smul_one
import Theorems.Thm_FullFormalization_convexOn_le_gradient
import Theorems.Thm_FullFormalization_d_mono
import Theorems.Thm_FullFormalization_d_nonneg
import Theorems.Thm_FullFormalization_d_one
import Theorems.Thm_FullFormalization_d_sub_pred
import Theorems.Thm_FullFormalization_d_succ_sub
import Theorems.Thm_FullFormalization_d_zero
import Theorems.Thm_FullFormalization_descent_lemma
import Theorems.Thm_FullFormalization_differentiable_inner_const
import Theorems.Thm_FullFormalization_differentiable_scaled
import Theorems.Thm_FullFormalization_endpoint_identity
import Theorems.Thm_FullFormalization_gradient_add_const
import Theorems.Thm_FullFormalization_gradient_congr
import Theorems.Thm_FullFormalization_gradient_const_add
import Theorems.Thm_FullFormalization_gradient_inner_const
import Theorems.Thm_FullFormalization_gradient_normalized
import Theorems.Thm_FullFormalization_gradient_scaled
import Theorems.Thm_FullFormalization_gradient_sub
import Theorems.Thm_FullFormalization_gradient_sub_inner
import Theorems.Thm_FullFormalization_h_at_N
import Theorems.Thm_FullFormalization_h_last
import Theorems.Thm_FullFormalization_h_last_prime
import Theorems.Thm_FullFormalization_h_pos
import Theorems.Thm_FullFormalization_h_rec
import Theorems.Thm_FullFormalization_hasFDerivAt_scaledArg
import Theorems.Thm_FullFormalization_initial_identity
import Theorems.Thm_FullFormalization_interior_identity
import Theorems.Thm_FullFormalization_mom_zero
import Theorems.Thm_FullFormalization_nagX_succ
import Theorems.Thm_FullFormalization_nagX_succ_prime
import Theorems.Thm_FullFormalization_nagX_zero
import Theorems.Thm_FullFormalization_nagY_succ
import Theorems.Thm_FullFormalization_nagY_succ_one
import Theorems.Thm_FullFormalization_nagY_zero
import Theorems.Thm_FullFormalization_nag_upper_bound_normalized
import Theorems.Thm_FullFormalization_scaledArg_add_smul
import Theorems.Thm_FullFormalization_scaledArg_apply
import Theorems.Thm_FullFormalization_scaled_apply
import Theorems.Thm_FullFormalization_tau_eq_inv
import Theorems.Thm_FullFormalization_tau_one
import Theorems.Thm_FullFormalization_tau_pos
import Theorems.Thm_FullFormalization_telescope
import Theorems.Thm_FullFormalization_terminal_identity
import Theorems.Thm_FullFormalization_toDual_smul_real
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

theorem solution {f : E → ℝ} {L R : ℝ} {x₀ xstar : E}
    (A : Admissible L R f x₀ xstar) (hR : 0 < R) (N : ℕ) (hN : 1 ≤ N) :
    f (nagX f L x₀ N) - f xstar ≤ 2 * L * R ^ 2 / ((N : ℝ) ^ 2 + 7 * (N : ℝ) + 4) := by
  have hL : 0 < L := A.L_pos
  have hLne : L ≠ 0 := ne_of_gt hL
  have hRne : R ≠ 0 := ne_of_gt hR
  -- the normalised function of source §1: `x⋆ ↦ 0`, `f⋆ ↦ 0`, `L ↦ 1`
  let fN : E → ℝ := fun y => (1 / (L * R ^ 2)) * (f (xstar + R • y) - f xstar)
  have hfNdef : fN = fun y : E => (1 / (L * R ^ 2)) * (f (xstar + R • y) - f xstar) := rfl
  -- `f = fun x => f x⋆ + scaled L R x⋆ fN x`
  have hfe : f = fun z => f xstar + scaled L R xstar fN z := by
    funext z
    simp only [fN, scaled_apply, scaledArg_apply]
    rw [show xstar + R • ((1 / R) • (z - xstar)) = z by
      rw [smul_smul, mul_one_div, div_self hRne, one_smul]
      abel]
    field_simp
    ring
  -- the gradient of `f` in terms of the normalised one
  have hdiffN : Differentiable ℝ fN := by
    rw [hfNdef]
    have h1 : Differentiable ℝ (fun z : E => xstar + R • z) := by fun_prop
    exact ((A.differentiable.comp h1).sub_const (f xstar)).const_mul _
  have hgradN : ∀ y : E, ∇ fN y = (1 / (L * R)) • ∇ f (xstar + R • y) := by
    intro y
    rw [gradient_congr hfNdef y]
    exact gradient_normalized A.differentiable hL hR xstar y
  have hgrad : ∀ z : E, ∇ f z = (L * R) • ∇ fN (scaledArg R xstar z) := by
    intro z
    rw [gradient_congr hfe z,
      gradient_const_add (differentiable_scaled L R xstar hdiffN) (f xstar) z,
      gradient_scaled hL hR hdiffN z]
  -- `∇f(x⋆) = 0`: `x⋆` is a minimiser of a differentiable function
  have hgrad0 : ∇ f xstar = 0 := by
    have hmin : IsMinOn f Set.univ xstar := isMinOn_iff.mpr (fun x _ => A.isMin x)
    have hloc : IsLocalMin f xstar := hmin.isLocalMin (by simp)
    rw [gradient, hloc.fderiv_eq_zero, map_zero]
  -- the fields of `NormalizedAtZero fN`
  have hN0 : fN 0 = 0 := by
    simp only [fN, smul_zero, add_zero, sub_self, mul_zero]
  have hNgrad0 : ∇ fN 0 = 0 := by
    rw [hgradN 0, show xstar + R • (0 : E) = xstar by simp, hgrad0, smul_zero]
  have hφconv : ConvexOn ℝ Set.univ (fun z : E => f (xstar + R • z)) := by
    have h := ConvexOn.comp_affineMap (affineShift R xstar) A.convex
    rw [Set.preimage_univ] at h
    simpa [Function.comp_def, affineShift] using h
  have hsub : ConvexOn ℝ Set.univ (fun z : E => f (xstar + R • z) - f xstar) := by
    have hfun : (fun z : E => f (xstar + R • z) - f xstar)
        = ((fun z : E => f (xstar + R • z)) + fun _ : E => (-f xstar)) := by
      funext z
      simp only [Pi.add_apply, sub_eq_add_neg]
    rw [hfun]
    exact hφconv.add_const (-f xstar)
  have hconvN : ConvexOn ℝ Set.univ fN := by
    have h := ConvexOn.smul (s := Set.univ) (c := 1 / (L * R ^ 2)) (by positivity) hsub
    have hfun : fN = fun z : E => (1 / (L * R ^ 2)) • (f (xstar + R • z) - f xstar) := by
      funext z
      simp only [fN, smul_eq_mul]
    rw [hfun]
    exact h
  have hsmN : ∀ a b : E, ‖∇ fN a - ∇ fN b‖ ≤ ‖a - b‖ := by
    intro a b
    have hpos : 0 < 1 / (L * R) := by positivity
    rw [hgradN a, hgradN b, ← smul_sub, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    have hsm := A.smooth (xstar + R • a) (xstar + R • b)
    have hnorm : ‖(xstar + R • a) - (xstar + R • b)‖ = R * ‖a - b‖ := by
      rw [show (xstar + R • a) - (xstar + R • b) = R • (a - b) by rw [smul_sub]; abel]
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos hR]
    calc (1 / (L * R)) * ‖∇ f (xstar + R • a) - ∇ f (xstar + R • b)‖
        ≤ (1 / (L * R)) * (L * ‖(xstar + R • a) - (xstar + R • b)‖) :=
          mul_le_mul_of_nonneg_left hsm (le_of_lt hpos)
      _ = ‖a - b‖ := by rw [hnorm]; field_simp
  have hminN : ∀ y : E, fN 0 ≤ fN y := by
    intro y
    rw [hN0]
    simp only [fN]
    apply mul_nonneg (by positivity)
    have := A.isMin (xstar + R • y)
    linarith
  have hfN : NormalizedAtZero fN :=
    ⟨hconvN, hdiffN, hsmN, hN0, hNgrad0, hminN⟩
  -- the trajectories correspond: `x_k = x⋆ + R · x_k^N`
  let r : E := (1 / R) • (x₀ - xstar)
  have hr_norm : ‖r‖ ≤ 1 := by
    have hpos : 0 < 1 / R := by positivity
    simp only [r, norm_smul, Real.norm_eq_abs, abs_of_pos hpos]
    calc (1 / R) * ‖x₀ - xstar‖ ≤ (1 / R) * R :=
          mul_le_mul_of_nonneg_left A.within_radius (le_of_lt hpos)
      _ = 1 := by rw [one_div, inv_mul_cancel₀ hRne]
  have htraj : ∀ k, nagX f L x₀ k = xstar + R • nagX fN 1 r k ∧
      nagY f L x₀ k = xstar + R • nagY fN 1 r k := by
    intro k
    induction k with
    | zero =>
        constructor
        · show x₀ = xstar + R • r
          simp only [r]
          rw [smul_smul, mul_one_div, div_self hRne, one_smul]
          abel
        · show x₀ = xstar + R • r
          simp only [r]
          rw [smul_smul, mul_one_div, div_self hRne, one_smul]
          abel
    | succ k ih =>
        obtain ⟨hxk, hyk⟩ := ih
        have hY : nagY f L x₀ (k + 1) = xstar + R • nagY fN 1 r (k + 1) := by
          rw [nagY_succ f L x₀ k, hxk, hgrad, nagY_succ fN 1 r k, one_div_one, one_smul,
            scaledArg_add_smul R hRne, smul_smul]
          have hc : (1 / L) * (L * R) = R := by field_simp
          rw [hc, smul_sub]
          abel
        refine ⟨?_, hY⟩
        rw [nagX_succ f L x₀ k, hY, hyk, nagX_succ fN 1 r k]
        have hd1 : (xstar + R • nagY fN 1 r (k + 1)) - (xstar + R • nagY fN 1 r k)
            = R • (nagY fN 1 r (k + 1) - nagY fN 1 r k) := by
          rw [smul_sub]
          abel
        have hd2 : mom k • (R • (nagY fN 1 r (k + 1) - nagY fN 1 r k))
            = R • (mom k • (nagY fN 1 r (k + 1) - nagY fN 1 r k)) :=
          smul_comm (mom k) R _
        rw [hd1, hd2, smul_add]
        abel
  -- assemble
  have hkey : f (nagX f L x₀ N) - f xstar = L * R ^ 2 * fN (nagX fN 1 r N) := by
    rw [(htraj N).1]
    simp only [fN]
    field_simp
  have hb := nag_upper_bound_normalized hfN r N hN
  rw [hfN.value_at_zero, sub_zero] at hb
  have hrsq : ‖r‖ ^ 2 ≤ 1 := by nlinarith [hr_norm, norm_nonneg r]
  have hmain : fN (nagX fN 1 r N) ≤ tau N := by
    have := mul_le_of_le_one_right (le_of_lt (tau_pos N)) hrsq
    linarith
  calc f (nagX f L x₀ N) - f xstar = L * R ^ 2 * fN (nagX fN 1 r N) := hkey
    _ ≤ L * R ^ 2 * tau N := mul_le_mul_of_nonneg_left hmain (by positivity)
    _ = 2 * L * R ^ 2 / ((N : ℝ) ^ 2 + 7 * (N : ℝ) + 4) := by rw [tau]; ring
