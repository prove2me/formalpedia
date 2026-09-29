-- Prove2me | solution 1 for FamousTheorems.implicit_function_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:36:18.213761+00:00
-- url     : https://prove2.me/submissions/7c32cebc-06fc-4b77-86aa-d7b05970b6d5

import Mathlib

open scoped ContDiff

theorem solution {𝕜 : Type*} [RCLike 𝕜] {E₁ E₂ F : Type*} [NormedAddCommGroup E₁] [NormedSpace 𝕜 E₁]
    [CompleteSpace E₁] [NormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [CompleteSpace E₂] [NormedAddCommGroup F]
    [NormedSpace 𝕜 F] [CompleteSpace F] {f : E₁ × E₂ → F} {u : E₁ × E₂} {n : ℕ∞ω} (cdf : ContDiffAt 𝕜 n f u)
    (pn : n ≠ 0) (if₂ : (fderiv 𝕜 f u ∘L ContinuousLinearMap.inr 𝕜 E₁ E₂).IsInvertible) :
    ∃ ψ : E₁ → E₂, ψ u.1 = u.2 ∧ (∀ᶠ v in nhds u, f v = f u ↔ ψ v.1 = v.2) ∧ ContDiffAt 𝕜 n ψ u.1 :=
  ⟨cdf.implicitFunction pn if₂, cdf.implicitFunction_apply_self pn if₂,
    cdf.eventually_apply_eq_iff_implicitFunction pn if₂, cdf.contDiffAt_implicitFunction pn if₂⟩
