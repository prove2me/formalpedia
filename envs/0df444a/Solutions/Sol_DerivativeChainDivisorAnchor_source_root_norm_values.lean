-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.source_root_norm_values
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:43:35.385927+00:00
-- url     : https://prove2.me/submissions/e4470b13-a409-4815-9b01-4bfcf01f544e

import Mathlib
import Definitions.Def_DerivativeChainGini_DivisorActualFamily
import Definitions.Def_DerivativeChainGini_GiniBinomialFamily
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainDivisorAnchor
end DerivativeChainDivisorAnchor
namespace DerivativeChainGini
end DerivativeChainGini
namespace DerivativeChainGiniCircle
end DerivativeChainGiniCircle
namespace DerivativeChainGiniFamily
end DerivativeChainGiniFamily
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
open scoped BigOperators
open Polynomial
namespace DerivativeChainGiniFamily
noncomputable section






theorem base_monic (n : ℕ) : (base n).Monic := by
  simpa [base] using monic_X_pow_sub_C (R := ℂ) 1 (n := n+2) (by omega)





























end
end DerivativeChainGiniFamily


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
namespace DerivativeChainDivisorAnchor
noncomputable section

theorem scaled_binomial (n : ℕ) (r : ℂ) :
    (base n).scaleRoots r = X^(n+2)-C (r^(n+2)) := by
  ext i
  rw [coeff_scaleRoots, base_degree]
  simp only [base, coeff_sub, coeff_X_pow, coeff_one, coeff_C]
  by_cases hi : i=n+2
  · subst i
    simp
  by_cases hi0 : i=0
  · subst i
    simp
  · simp [hi, hi0, eq_comm]




theorem anchor_source_monic (n k : ℕ) (a : ℝ) : (anchorSource n k a).Monic := by
  exact ((monic_scaleRoots_iff _).mpr (base_monic n)).mul ((base_monic n).pow _)













end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor

attribute [local instance] Classical.propDecidable













theorem solution (n k : ℕ) (a : ℝ) (ha : 0 < a)
    (i : (anchorSource n k a).roots) : ‖(i:ℂ)‖=a ∨ ‖(i:ℂ)‖=1 := by
  have hi := (mem_roots (anchor_source_monic n k a).ne_zero).mp (Multiset.coe_mem (x := i))
  change (anchorSource n k a).eval (i:ℂ)=0 at hi
  have hscaled : ((base n).scaleRoots (a:ℂ)).eval (i:ℂ) = (i:ℂ)^(n+2)-(a:ℂ)^(n+2) := by
    rw [scaled_binomial]
    simp
  simp only [anchorSource, eval_mul, eval_pow] at hi
  rw [hscaled] at hi
  simp only [base, eval_sub, eval_pow, eval_X, eval_one] at hi
  rcases mul_eq_zero.mp hi with hi | hi
  · have he : (i:ℂ)^(n+2) = (a:ℂ)^(n+2) := sub_eq_zero.mp hi
    have hn := congrArg norm he
    simp only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha] at hn
    exact Or.inl ((pow_left_inj₀ (norm_nonneg _) ha.le (by omega : n+2 ≠ 0)).mp hn)
  · have he : (i:ℂ)^(n+2)=1 := sub_eq_zero.mp (eq_zero_of_pow_eq_zero hi)
    have hn := congrArg norm he
    simp only [norm_pow, norm_one] at hn
    have heq : ‖(i:ℂ)‖=1 := (pow_left_inj₀ (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 1)
      (by omega : n+2 ≠ 0)).mp (by simpa using hn)
    exact Or.inr heq
