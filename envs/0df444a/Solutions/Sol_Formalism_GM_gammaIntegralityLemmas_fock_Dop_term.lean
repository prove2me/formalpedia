-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.fock_Dop_term
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:44.047661+00:00
-- url     : https://prove2.me/submissions/7da7d207-7e48-4b14-ac7e-a84539b58b25

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_fock_monomial
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_Dop_pow_monomial_add
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_wf_add_single_eq
import Theorems.Thm_Formalism_GM_gammaIntegralityLemmas_X_pow_mul_monomial

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (x y : σ) (hxy : x ≠ y) (a a' m : ℕ) (β₀ β₀' : σ →₀ ℕ) (h h' : ℚ_[p]) :
    Formalism.GM.M.fock p ((Dop x y ^ a) (X y ^ m * monomial (β₀ + a • (Finsupp.single x 1 + Finsupp.single y 1)) h))
      ((Dop x y ^ a') (X y ^ m * monomial (β₀' + a' • (Finsupp.single x 1 + Finsupp.single y 1)) h')) =
    if β₀ = β₀' then
      h * h' * (((β₀ x + a).descFactorial a : ℕ) : ℚ_[p]) * (((β₀ x + a').descFactorial a' : ℕ) : ℚ_[p]) *
        wf (β₀ + Finsupp.single y a) * (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) *
        (m.factorial : ℚ_[p]) * ((((m + (β₀ y + a'))).descFactorial a' : ℕ) : ℚ_[p])
    else 0 := by
  rw [X_pow_mul_monomial, X_pow_mul_monomial]
  have e1 : β₀ + a • (Finsupp.single x 1 + Finsupp.single y 1) + Finsupp.single y m =
      (β₀ + Finsupp.single y m) + a • (Finsupp.single x 1 + Finsupp.single y 1) := by abel
  have e2 : β₀' + a' • (Finsupp.single x 1 + Finsupp.single y 1) + Finsupp.single y m =
      (β₀' + Finsupp.single y m) + a' • (Finsupp.single x 1 + Finsupp.single y 1) := by abel
  rw [e1, e2, Dop_pow_monomial_add x y hxy, Dop_pow_monomial_add x y hxy, fock_monomial]
  have hx : ∀ δ : σ →₀ ℕ, (δ + Finsupp.single y m) x = δ x := by
    intro δ; simp [Finsupp.single_apply, Ne.symm hxy]
  have hy : ∀ δ : σ →₀ ℕ, (δ + Finsupp.single y m) y = δ y + m := by
    intro δ; simp
  rw [hx, hx, hy, hy]
  by_cases hb : β₀ = β₀'
  · subst hb
    rw [if_pos rfl, if_pos rfl]

    have hk : ((β₀ y).factorial : ℚ_[p]) ≠ 0 := by exact_mod_cast (Nat.factorial_pos _).ne'
    have w1 := wf_add_single_eq (p := p) β₀ y m
    have w2 := wf_add_single_eq (p := p) β₀ y a
    have f1 : ((β₀ y + m).factorial : ℚ_[p]) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) =
        ((β₀ y + m + a).factorial : ℚ_[p]) := by
      have := Nat.factorial_mul_descFactorial (show a ≤ β₀ y + m + a by omega)
      rw [show β₀ y + m + a - a = β₀ y + m by omega] at this
      exact_mod_cast this
    have f2 : (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) * (m.factorial : ℚ_[p]) *
        ((β₀ y + a).factorial : ℚ_[p]) = ((β₀ y + m + a).factorial : ℚ_[p]) := by
      have := Nat.add_choose_mul_factorial_mul_factorial m (β₀ y + a)
      rw [show m + (β₀ y + a) = β₀ y + m + a by ring] at this
      rw [show m + (β₀ y + a) = β₀ y + m + a by ring]
      exact_mod_cast this
    have key : wf (p := p) (β₀ + Finsupp.single y m) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) =
        wf (β₀ + Finsupp.single y a) * (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) * (m.factorial : ℚ_[p]) := by
      apply mul_right_cancel₀ hk
      calc wf (p := p) (β₀ + Finsupp.single y m) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) * ((β₀ y).factorial : ℚ_[p])
          = (wf (p := p) (β₀ + Finsupp.single y m) * ((β₀ y).factorial : ℚ_[p])) *
              (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) := by ring
        _ = wf β₀ * (((β₀ y + m).factorial : ℚ_[p]) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p])) := by
              rw [w1]; ring
        _ = wf β₀ * ((β₀ y + m + a).factorial : ℚ_[p]) := by rw [f1]
        _ = (wf (p := p) (β₀ + Finsupp.single y a) * ((β₀ y).factorial : ℚ_[p])) *
              (((m + (β₀ y + a)).choose (β₀ y + a) : ℕ) : ℚ_[p]) * (m.factorial : ℚ_[p]) := by
              rw [w2, ← f2]; ring
        _ = _ := by ring
    rw [show m + (β₀ y + a') = β₀ y + m + a' by ring]
    calc h * (((β₀ x + a).descFactorial a : ℕ) : ℚ_[p]) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p]) *
          (h' * (((β₀ x + a').descFactorial a' : ℕ) : ℚ_[p]) * (((β₀ y + m + a').descFactorial a' : ℕ) : ℚ_[p])) *
          wf (β₀ + Finsupp.single y m)
        = h * h' * (((β₀ x + a).descFactorial a : ℕ) : ℚ_[p]) * (((β₀ x + a').descFactorial a' : ℕ) : ℚ_[p]) *
          (wf (p := p) (β₀ + Finsupp.single y m) * (((β₀ y + m + a).descFactorial a : ℕ) : ℚ_[p])) *
          (((β₀ y + m + a').descFactorial a' : ℕ) : ℚ_[p]) := by ring
      _ = _ := by rw [key]; ring
  · have : β₀ + Finsupp.single y m ≠ β₀' + Finsupp.single y m := fun h'' => hb (add_right_cancel h'')
    rw [if_neg this, if_neg hb]
end Formalism.GM.gammaIntegralityLemmas
