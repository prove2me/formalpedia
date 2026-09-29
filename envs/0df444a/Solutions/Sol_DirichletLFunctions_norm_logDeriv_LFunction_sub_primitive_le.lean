-- Prove2me | solution 1 for DirichletLFunctions.norm_logDeriv_LFunction_sub_primitive_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T16:32:47.209204+00:00
-- url     : https://prove2.me/submissions/9ed90145-8c53-4409-b27c-a05c315a6b17

import Mathlib

open DirichletCharacter

instance instNeZeroConductorP2M {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

set_option maxHeartbeats 2000000

-- ===== Salt.SW.EulerBridge =====
section
/-
Copyright (c) 2026 Jason Hickey. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Hickey, Claude
-/

/-!
# The SW rung, node S3b — the imprimitive→primitive logarithmic-derivative bridge

Design: `docs/blueprints/sw.md`, wave S3 (Fable split: S3b). The S2 zero-theory
cluster (ZeroCount/Growth/PartialFractions/BCBound/MaxModulus) is stated for
*primitive* characters only, whereas the SW gate quantifies over **all** `χ mod q`.
This module bridges the gap: for `χ : DirichletCharacter ℂ q` induced by the
primitive character `χ₁ := χ.primitiveCharacter` of level `f₁ := χ.conductor`
(`f₁ ∣ q`), it transfers the log-derivative and the zero set from `χ₁` to `χ`
through the finite Euler correction, with an explicit `≤ log q` bound on the
correction (constant `C₅ = 0`).

## The mechanism

mathlib's `DirichletCharacter.LFunction_changeLevel` gives, for `χ ≠ 1 ∨ s ≠ 1`,
`L(χ, s) = L(χ₁, s) · ∏_{p ∣ q} (1 − χ₁(p) p^{−s})`
(via `changeLevel_primitiveCharacter : changeLevel χ.conductor_dvd_level χ₁ = χ`).
The correction factors are packaged as `eulerFactor` / `eulerCorr`. Taking
`logDeriv` of the product (mathlib `logDeriv_mul`, `logDeriv_prod`) turns the
multiplicative relation into the additive
`logDeriv L(χ) = logDeriv L(χ₁) + Σ_{p ∣ q} logDeriv(1 − χ₁(p) p^{−s})`, valid
wherever `L(χ₁) ≠ 0` and the factors are non-vanishing (automatic for `Re s > 0`,
since `‖χ₁(p) p^{−s}‖ < 1`).

## The bound

Each correction term is `χ₁(p) log p · p^{−s} / (1 − χ₁(p) p^{−s})`, of norm
`≤ log p · p^{−σ} / (1 − p^{−σ}) ≤ log p` for `σ = Re s ≥ 1` (the key fact
`p^{−σ} ≤ 1/2` for `p ≥ 2, σ ≥ 1`). Summing over `p ∈ q.primeFactors` and using
`∏_{p ∣ q} p ∣ q` (`Nat.prod_primeFactors_dvd`) gives `Σ log p = log(∏ p) ≤ log q`.
So `C₅ = 0`:
`‖logDeriv L(χ) s − logDeriv L(χ₁) s‖ ≤ log q` on `Re s ≥ 1`.

## Exports (what S3c/S3d consume)

* `LFunction_eq_primitive_mul` — the pointwise product relation `L(χ) = L(χ₁)·∏`.
* `eulerCorr_ne_zero` — the correction is non-vanishing on `Re s > 0`.
* `logDeriv_LFunction_eq` — the additive log-derivative identity.
* `LFunction_eq_zero_iff_primitive` — the zero-set transfer on `Re s > 0`
  (`L(χ) s = 0 ↔ L(χ₁) s = 0`): the S3 zero-free region transfers verbatim.
* `norm_logDeriv_LFunction_sub_primitive_le` — the `≤ log q` correction bound on
  `Re s ≥ 1` (`C₅ = 0`).
-/

namespace Salt.SW

open Complex DirichletCharacter Finset Filter
open scoped Topology

/-- The conductor of a Dirichlet character mod `q` (with `q ≠ 0`) is itself nonzero; this
makes `LFunction χ.primitiveCharacter` (which needs `[NeZero χ.conductor]`) available. -/
instance instNeZeroConductor {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} :
    NeZero χ.conductor := ⟨χ.conductor_ne_zero⟩

/-! ## 1. The Euler correction factors -/

/-- The `p`-th Euler correction factor `s ↦ 1 − ψ(p)·p^{−s}` for a character `ψ`.
When `ψ` is `χ.primitiveCharacter`, the finite product of these over `p ∣ q` is the
ratio `L(χ)/L(χ₁)` (see `LFunction_eq_primitive_mul`). -/
noncomputable def eulerFactor {M : ℕ} (ψ : DirichletCharacter ℂ M) (p : ℕ) : ℂ → ℂ :=
  fun s => 1 - ψ p * (p : ℂ) ^ (-s)

/-- The full Euler correction `∏_{p ∣ q} (1 − χ₁(p) p^{−s})` relating `L(χ)` to
`L(χ₁)` for `χ₁ = χ.primitiveCharacter`. -/
noncomputable def eulerCorr {q : ℕ} (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∏ p ∈ q.primeFactors, eulerFactor χ.primitiveCharacter p s

/-- The Euler factor is entire: `s ↦ 1 − ψ(p)·p^{−s}` is differentiable with
derivative `ψ(p)·p^{−s}·log p`. -/
theorem hasDerivAt_eulerFactor {M : ℕ} (ψ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    (s : ℂ) :
    HasDerivAt (eulerFactor ψ p) (ψ p * (p : ℂ) ^ (-s) * Complex.log p) s := by
  have hpc : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hc : HasDerivAt (fun z : ℂ => (p : ℂ) ^ (-z))
      ((p : ℂ) ^ (-s) * Complex.log p * (-1)) s :=
    ((hasDerivAt_id s).neg).const_cpow (Or.inl hpc)
  have key := (hasDerivAt_const s (1 : ℂ)).sub (hc.const_mul (ψ p))
  have hval : (0 : ℂ) - ψ p * ((p : ℂ) ^ (-s) * Complex.log p * (-1))
      = ψ p * (p : ℂ) ^ (-s) * Complex.log p := by ring
  rw [hval] at key
  exact key

/-- The Euler factor is differentiable everywhere. -/
theorem differentiableAt_eulerFactor {M : ℕ} (ψ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    (s : ℂ) : DifferentiableAt ℂ (eulerFactor ψ p) s :=
  (hasDerivAt_eulerFactor ψ hp s).differentiableAt

/-- The Euler factor is non-vanishing on `Re s > 0`: `‖ψ(p)·p^{−s}‖ < 1` there. -/
theorem eulerFactor_ne_zero {M : ℕ} (ψ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 0 < s.re) : eulerFactor ψ p s ≠ 0 := by
  have hP0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hP1 : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp.one_lt
  -- `‖ψ(p)·p^{−s}‖ = ‖ψ p‖ · p^{−σ} ≤ p^{−σ} < 1`.
  have hcpow : ‖(p : ℂ) ^ (-s)‖ = (p : ℝ) ^ (-s.re) := by
    rw [show (p : ℂ) = ((p : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_cpow_eq_rpow_re_of_pos hP0, Complex.neg_re]
  have hlt1 : (p : ℝ) ^ (-s.re) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hP1 (by linarith)
  have hnorm : ‖ψ p * (p : ℂ) ^ (-s)‖ < 1 := by
    rw [norm_mul, hcpow]
    calc ‖ψ p‖ * (p : ℝ) ^ (-s.re) ≤ 1 * (p : ℝ) ^ (-s.re) := by
          gcongr; exact ψ.norm_le_one _
      _ = (p : ℝ) ^ (-s.re) := one_mul _
      _ < 1 := hlt1
  intro h
  rw [eulerFactor, sub_eq_zero] at h
  rw [← h, norm_one] at hnorm
  exact lt_irrefl 1 hnorm

/-- The Euler correction is non-vanishing on `Re s > 0`. -/
theorem eulerCorr_ne_zero {q : ℕ} (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 0 < s.re) :
    eulerCorr χ s ≠ 0 := by
  rw [eulerCorr, Finset.prod_ne_zero_iff]
  exact fun p hp => eulerFactor_ne_zero _ (Nat.prime_of_mem_primeFactors hp) hs

/-! ## 2. The product relation `L(χ) = L(χ₁)·∏` -/

/-- **The imprimitive→primitive product relation.** For `χ : DirichletCharacter ℂ q`
induced by `χ₁ = χ.primitiveCharacter`, and any `s` with `χ ≠ 1 ∨ s ≠ 1`,
`L(χ, s) = L(χ₁, s) · ∏_{p ∣ q} (1 − χ₁(p) p^{−s})`. Immediate from mathlib's
`LFunction_changeLevel` via `changeLevel_primitiveCharacter`. -/
theorem LFunction_eq_primitive_mul {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (h1 : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s = LFunction χ.primitiveCharacter s * eulerCorr χ s := by
  have h1' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases h1 with hχ | hs1
    · exact Or.inl fun hp => hχ (by
        rw [← changeLevel_primitiveCharacter χ, hp, changeLevel_one])
    · exact Or.inr hs1
  have h := LFunction_changeLevel χ.conductor_dvd_level χ.primitiveCharacter h1'
  rw [changeLevel_primitiveCharacter] at h
  rw [h]; rfl

/-! ## 3. The additive log-derivative identity -/

/-- **The log-derivative bridge (identity form).** Wherever `L(χ₁) ≠ 0` (and
`Re s > 0`, so the finite Euler factors are non-vanishing),
`logDeriv L(χ) s = logDeriv L(χ₁) s + Σ_{p ∣ q} logDeriv(1 − χ₁(p) p^{−s}) s`. -/
theorem logDeriv_LFunction_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) (hL₁ : LFunction χ.primitiveCharacter s ≠ 0) (h1 : χ ≠ 1 ∨ s ≠ 1) :
    logDeriv (LFunction χ) s
      = logDeriv (LFunction χ.primitiveCharacter) s
        + ∑ p ∈ q.primeFactors, logDeriv (eulerFactor χ.primitiveCharacter p) s := by
  have h1' : χ.primitiveCharacter ≠ 1 ∨ s ≠ 1 := by
    rcases h1 with hχ | hs1
    · exact Or.inl fun hp => hχ (by
        rw [← changeLevel_primitiveCharacter χ, hp, changeLevel_one])
    · exact Or.inr hs1
  -- `L(χ)` agrees with the product `L(χ₁)·eulerCorr χ` on a neighbourhood of `s`.
  have hev : LFunction χ =ᶠ[𝓝 s] (fun z => LFunction χ.primitiveCharacter z * eulerCorr χ z) := by
    rcases h1 with hχ | hs1
    · exact Filter.Eventually.of_forall
        (fun z => LFunction_eq_primitive_mul χ (Or.inl hχ))
    · refine Filter.eventually_of_mem (isOpen_compl_singleton.mem_nhds (by simpa using hs1))
        (fun z (hz : z ∈ ({1}ᶜ : Set ℂ)) => ?_)
      exact LFunction_eq_primitive_mul χ (Or.inr (by simpa using hz))
  have hlog_eq : logDeriv (LFunction χ) s
      = logDeriv (fun z => LFunction χ.primitiveCharacter z * eulerCorr χ z) s := by
    rw [logDeriv_apply, logDeriv_apply, hev.deriv_eq, hev.eq_of_nhds]
  have hdL₁ : DifferentiableAt ℂ (LFunction χ.primitiveCharacter) s :=
    differentiableAt_LFunction _ _ h1'.symm
  have hdcorr : DifferentiableAt ℂ (eulerCorr χ) s :=
    DifferentiableAt.fun_finsetProd
      (fun p hp => differentiableAt_eulerFactor _ (Nat.prime_of_mem_primeFactors hp) s)
  have hcorr_ne : eulerCorr χ s ≠ 0 := eulerCorr_ne_zero χ hs
  have hprod : logDeriv (eulerCorr χ) s
      = ∑ p ∈ q.primeFactors, logDeriv (eulerFactor χ.primitiveCharacter p) s :=
    logDeriv_prod (fun p hp => eulerFactor_ne_zero _ (Nat.prime_of_mem_primeFactors hp) hs)
      (fun p hp => differentiableAt_eulerFactor _ (Nat.prime_of_mem_primeFactors hp) s)
  rw [hlog_eq, logDeriv_mul s hL₁ hcorr_ne hdL₁ hdcorr, hprod]

/-! ## 4. The zero-set transfer -/

/-- **Zero-set transfer.** On `Re s > 0` (and `χ ≠ 1 ∨ s ≠ 1`),
`L(χ) s = 0 ↔ L(χ₁) s = 0`: the finite Euler factors are zero-free, so the S3
zero-free region transfers verbatim from the primitive character to `χ`. -/
theorem LFunction_eq_zero_iff_primitive {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : 0 < s.re) (h1 : χ ≠ 1 ∨ s ≠ 1) :
    LFunction χ s = 0 ↔ LFunction χ.primitiveCharacter s = 0 := by
  rw [LFunction_eq_primitive_mul χ h1, mul_eq_zero]
  refine ⟨fun h => h.resolve_right (eulerCorr_ne_zero χ hs), Or.inl⟩

/-! ## 5. The `≤ log q` correction bound (`C₅ = 0`) -/

/-- Per-factor bound: `‖logDeriv(1 − ψ(p) p^{−s})‖ ≤ log p` for `Re s ≥ 1`.
The term is `ψ(p) log p · p^{−s} / (1 − ψ(p) p^{−s})`, of norm
`≤ log p · p^{−σ}/(1 − p^{−σ}) ≤ log p` since `p^{−σ} ≤ 1/2` for `p ≥ 2, σ ≥ 1`. -/
theorem norm_logDeriv_eulerFactor_le {M : ℕ} (ψ : DirichletCharacter ℂ M) {p : ℕ} (hp : p.Prime)
    {s : ℂ} (hs : 1 ≤ s.re) : ‖logDeriv (eulerFactor ψ p) s‖ ≤ Real.log p := by
  have hP0 : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp.pos
  have hP1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.one_lt.le
  have hP2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hLnn : 0 ≤ Real.log p := Real.log_nonneg hP1
  have hcast : (p : ℂ) = ((p : ℝ) : ℂ) := (Complex.ofReal_natCast p).symm
  set pσ : ℝ := (p : ℝ) ^ (-s.re) with hpσ
  have hpσ0 : 0 < pσ := Real.rpow_pos_of_pos hP0 _
  -- `p^{−σ} ≤ 1/2`: from `p^{−σ}·p^σ = 1` and `p^σ ≥ p^1 = p ≥ 2`.
  have hge : (2 : ℝ) ≤ (p : ℝ) ^ s.re :=
    le_trans hP2 (by simpa using Real.rpow_le_rpow_of_exponent_le hP1 hs)
  have hprod1 : pσ * (p : ℝ) ^ s.re = 1 := by
    rw [hpσ, ← Real.rpow_add hP0, neg_add_cancel, Real.rpow_zero]
  have hpσ_half : pσ ≤ 1 / 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hge hpσ0.le]
  have hden : 0 < 1 - pσ := by linarith
  -- `‖deriv‖ ≤ pσ · log p`, from the explicit derivative.
  have hderiv : deriv (eulerFactor ψ p) s = ψ p * (p : ℂ) ^ (-s) * Complex.log p :=
    (hasDerivAt_eulerFactor ψ hp s).deriv
  have hcpow : ‖(p : ℂ) ^ (-s)‖ = pσ := by
    rw [hpσ, hcast, Complex.norm_cpow_eq_rpow_re_of_pos hP0, Complex.neg_re]
  have hlogp : ‖Complex.log (p : ℂ)‖ = Real.log p := by
    rw [hcast, ← Complex.ofReal_log hP0.le, Complex.norm_of_nonneg (Real.log_nonneg hP1)]
  have hnum : ‖deriv (eulerFactor ψ p) s‖ ≤ pσ * Real.log p := by
    rw [hderiv, norm_mul, norm_mul, hcpow, hlogp]
    calc ‖ψ p‖ * pσ * Real.log p ≤ 1 * pσ * Real.log p := by gcongr; exact ψ.norm_le_one _
      _ = pσ * Real.log p := by ring
  -- `‖factor‖ ≥ 1 − pσ`.
  have hfac : 1 - pσ ≤ ‖eulerFactor ψ p s‖ := by
    have hX : ‖ψ p * (p : ℂ) ^ (-s)‖ ≤ pσ := by
      rw [norm_mul, hcpow]
      calc ‖ψ p‖ * pσ ≤ 1 * pσ := by gcongr; exact ψ.norm_le_one _
        _ = pσ := one_mul _
    have hsub : ‖(1 : ℂ)‖ - ‖ψ p * (p : ℂ) ^ (-s)‖ ≤ ‖eulerFactor ψ p s‖ := by
      rw [eulerFactor]; exact norm_sub_norm_le _ _
    rw [norm_one] at hsub
    linarith
  -- Assemble: `‖logDeriv‖ = ‖deriv‖/‖factor‖ ≤ log p`.
  have hfac0 : 0 < ‖eulerFactor ψ p s‖ := lt_of_lt_of_le hden hfac
  rw [logDeriv_apply, norm_div, div_le_iff₀ hfac0]
  calc ‖deriv (eulerFactor ψ p) s‖
      ≤ pσ * Real.log p := hnum
    _ ≤ Real.log p * (1 - pσ) := by
        nlinarith [mul_nonneg hLnn (show (0 : ℝ) ≤ 1 - 2 * pσ by linarith)]
    _ ≤ Real.log p * ‖eulerFactor ψ p s‖ := mul_le_mul_of_nonneg_left hfac hLnn

/-- **The correction bound (`C₅ = 0`).** For `χ` induced by `χ₁ = χ.primitiveCharacter`,
wherever `L(χ₁) ≠ 0` on `Re s ≥ 1`,
`‖logDeriv L(χ) s − logDeriv L(χ₁) s‖ ≤ log q`. This is the S3d feed: the
imprimitive log-derivative differs from the primitive one by at most `log q`. -/
theorem norm_logDeriv_LFunction_sub_primitive_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    {s : ℂ} (hs : 1 ≤ s.re) (hL₁ : LFunction χ.primitiveCharacter s ≠ 0) (h1 : χ ≠ 1 ∨ s ≠ 1) :
    ‖logDeriv (LFunction χ) s - logDeriv (LFunction χ.primitiveCharacter) s‖ ≤ Real.log q := by
  have hsre : (0 : ℝ) < s.re := lt_of_lt_of_le one_pos hs
  rw [logDeriv_LFunction_eq χ hsre hL₁ h1, add_sub_cancel_left]
  calc ‖∑ p ∈ q.primeFactors, logDeriv (eulerFactor χ.primitiveCharacter p) s‖
      ≤ ∑ p ∈ q.primeFactors, ‖logDeriv (eulerFactor χ.primitiveCharacter p) s‖ :=
        norm_sum_le _ _
    _ ≤ ∑ p ∈ q.primeFactors, Real.log p :=
        Finset.sum_le_sum
          (fun p hp => norm_logDeriv_eulerFactor_le _ (Nat.prime_of_mem_primeFactors hp) hs)
    _ = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
        rw [Real.log_prod]
        intro p hp
        exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos.ne'
    _ ≤ Real.log q := by
        apply Real.log_le_log
        · apply Finset.prod_pos
          exact fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
        · rw [← Nat.cast_prod]
          exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q))
            (Nat.prod_primeFactors_dvd q)

end Salt.SW

end




theorem solution {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ} (hs : 1 ≤ s.re)
    (hL₁ : LFunction χ.primitiveCharacter s ≠ 0) (h1 : χ ≠ 1 ∨ s ≠ 1) :
    ‖logDeriv (LFunction χ) s - logDeriv (LFunction χ.primitiveCharacter) s‖ ≤ Real.log q :=
  Salt.SW.norm_logDeriv_LFunction_sub_primitive_le χ hs hL₁ h1

