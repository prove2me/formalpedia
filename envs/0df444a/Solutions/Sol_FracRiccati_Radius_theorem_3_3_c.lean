-- Prove2me | solution 1 for FracRiccati.Radius.theorem_3_3_c
-- status  : ACCEPTED   (prove)
-- author  : @tianyipeng
-- created : 2026-11-03T04:58:21.37547+00:00
-- url     : https://prove2.me/submissions/5fab4cb5-84a3-4c9b-af33-c83a2fe7e573

import Mathlib
import Definitions.Def_FracRiccati_Radius_Coeff

namespace Aux_FRR_T33c
open FracRiccati.Radius

lemma coeff_rec (α : ℝ) (lam mu nu : ℂ) (j : ℕ) : coeff α lam mu nu (j + 2) =
    (lam * ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ)
      + mu * coeff α lam mu nu (j + 1)) *
      ((Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + 1) /
          Real.Gamma (α * ((j + 1 : ℕ) : ℝ) + α + 1) : ℝ) : ℂ) := by
  rw [coeff, Finset.sum_attach (Finset.Ico 1 (j + 1))
    (fun ℓ => coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ))]

lemma coeff_sign (α : ℝ) (lam mu nu : ℂ) (k : ℕ) :
    coeff α lam mu nu k = (-1 : ℂ) ^ (k - 1) * coeff α lam (-mu) nu k := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ => simp [coeff]
    | 1, _ => simp [coeff]
    | j + 2, ih =>
      rw [coeff_rec, coeff_rec, ih (j + 1) (by omega)]
      have hs : ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α lam mu nu ℓ * coeff α lam mu nu (j + 1 - ℓ)
          = (-1 : ℂ) ^ (j + 2 - 1) *
            ∑ ℓ ∈ Finset.Ico 1 (j + 1), coeff α lam (-mu) nu ℓ * coeff α lam (-mu) nu (j + 1 - ℓ) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro ℓ hℓ
        rw [Finset.mem_Ico] at hℓ
        rw [ih ℓ (by omega), ih (j + 1 - ℓ) (by omega)]
        have he : j + 2 - 1 = (ℓ - 1 + (j + 1 - ℓ - 1)) + 2 := by omega
        rw [he, pow_add, pow_add]
        ring
      rw [hs]
      have he2 : j + 2 - 1 = (j + 1 - 1) + 1 := by omega
      rw [he2, pow_succ]
      ring

end Aux_FRR_T33c

open FracRiccati.Radius Aux_FRR_T33c in
theorem solution (α : ℝ) (hα0 : 0 < α) (hα2 : α ≤ 2)
    (l m n : ℝ) (hl : 0 < l) (hn : 0 < n) (hm : m ≤ 0) :
    (∀ k : ℕ, 1 ≤ k →
      coeff α l m n k = (-1 : ℂ) ^ (k - 1) * coeff α l ((-m : ℝ) : ℂ) n k) ∧
    radius α (coeff α l m n) = radius α (coeff α l ((-m : ℝ) : ℂ) n) := by
  have key : ∀ k : ℕ, coeff α l m n k = (-1 : ℂ) ^ (k - 1) * coeff α l ((-m : ℝ) : ℂ) n k := by
    intro k
    rw [coeff_sign α l m n k]
    push_cast
    rfl
  refine ⟨fun k _ => key k, ?_⟩
  unfold radius
  congr 1
  funext k
  rw [key k, nnnorm_mul, nnnorm_pow, nnnorm_neg, nnnorm_one, one_pow, one_mul]
