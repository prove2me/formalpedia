-- Prove2me | solution 1 for DerivativeChainDivisorAnchor.anchor_source_derivative
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:54:36.064002+00:00
-- url     : https://prove2.me/submissions/c88cbfae-5f84-4e0f-9079-4c5fb6308cb0

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


















end
end DerivativeChainDivisorAnchor


set_option autoImplicit false
open scoped BigOperators
open Polynomial DerivativeChainGiniFamily
open DerivativeChainDivisorAnchor



















theorem solution (n k : ℕ) (hk : 2 ≤ k) (a b : ℝ)
    (hbq : b^(n+2) = (1+(k-1 : ℝ)*a^(n+2))/(k:ℝ)) :
    (anchorSource n k a).derivative = C ((n+2)*k : ℂ) * anchorChild n k b := by
  have hknat : k-1 = (k-2)+1 := by omega
  have hkR : (k:ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hrel : (k:ℂ)*(b:ℂ)^(n+2) = 1+((k:ℂ)-1)*(a:ℂ)^(n+2) := by
    have h := (eq_div_iff hkR).mp hbq
    have h' : (k:ℝ)*b^(n+2) = 1+((k:ℝ)-1)*a^(n+2) := by nlinarith
    exact_mod_cast h'
  have hC := congrArg (C : ℂ → ℂ[X]) hrel
  have hD : (base n).derivative = C (n+2 : ℂ)*X^(n+1) := by
    simp [base, derivative_pow, show n+2-1=n+1 by omega]
  have hDa : ((base n).scaleRoots (a:ℂ)).derivative = C (n+2 : ℂ)*X^(n+1) := by
    rw [scaled_binomial]
    simp [derivative_pow, show n+2-1=n+1 by omega]
  have hcast : ((k-1 : ℕ):ℂ) = (k:ℂ)-1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ k), Nat.cast_one]
  have hpow : (base n)^(k-1) = (base n)^(k-2)*base n := by rw [hknat, pow_succ]
  rw [anchorSource, anchorChild, derivative_mul, hDa, derivative_pow, hD,
    show k-1-1=k-2 by omega, hcast, hpow, scaled_binomial, scaled_binomial]
  simp only [base, map_mul, map_add, map_sub, map_pow, map_natCast, map_one, Polynomial.C_ofNat] at hC ⊢
  linear_combination ((n+2:ℂ[X])*X^(n+1)*(X^(n+2)-1)^(k-2))*hC
