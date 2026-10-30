-- Prove2me | solution 1 for DerivativeChainContinuation.derivative_centered_second_moment
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T18:09:24.036236+00:00
-- url     : https://prove2.me/submissions/7fb11c3a-56a0-4499-a022-74144b6d191b

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PolynomialMoments
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_monicDerivative_centered
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial

theorem multiset_second_newton {R : Type*} [CommRing R] (s : Multiset R) :
    s.sum^2 = (s.map fun z => z^2).sum + 2*s.esymm 2 := by
  induction s using Multiset.induction_on with
  | empty => simp [Multiset.esymm, Multiset.powersetCard_zero_right]
  | cons a s ih =>
    have hmul : (s.map fun x => a*x).sum = a*s.sum := by
      simpa using (Multiset.sum_map_mul_left (s := s) (a := a) (f := id))
    have hs : (a ::ₘ s).esymm 2 = s.esymm 2 + a*s.sum := by
      simp [Multiset.esymm, Multiset.powersetCard_cons, Multiset.powersetCard_one,
        hmul]
    simp only [Multiset.sum_cons, Multiset.map_cons, hs]
    linear_combination ih

theorem polynomial_second_newton_of_splits {F : Type*} [Field F]
    (p : Polynomial F) (hp : p.Monic) (hsplit : p.Splits)
    (hdeg : 2 ≤ p.natDegree) :
    (p.roots.map fun z => z^2).sum =
      p.roots.sum^2 - 2*p.coeff (p.natDegree-2) := by
  have hc := p.coeff_eq_esymm_roots_of_splits hsplit
    (k := p.natDegree-2) (Nat.sub_le _ _)
  have hd : p.natDegree-(p.natDegree-2)=2 := by omega
  simp only [hp.leadingCoeff, one_mul, hd, neg_one_sq, one_mul] at hc
  rw [hc]
  linear_combination -(multiset_second_newton p.roots)

theorem polynomial_second_newton (p : Polynomial ℂ) (hp : p.Monic)
    (hdeg : 2 ≤ p.natDegree) :
    (p.roots.map fun z => z^2).sum =
      p.roots.sum^2 - 2*p.coeff (p.natDegree-2) :=
  polynomial_second_newton_of_splits p hp (IsAlgClosed.splits p) hdeg


end DerivativeChainContinuation


set_option autoImplicit false
namespace DerivativeChainContinuation
open Polynomial



theorem monicDerivative_monic (p : Polynomial ℂ) (hp : p.Monic)
    (hn : p.natDegree ≠ 0) : (monicDerivative p).Monic := by
  apply monic_C_mul_of_mul_leadingCoeff_eq_one
  rw [leadingCoeff_derivative, hp.leadingCoeff, one_mul]
  exact inv_mul_cancel₀ (by exact_mod_cast hn)

theorem monicDerivative_natDegree (p : Polynomial ℂ) (hn : p.natDegree ≠ 0) :
    (monicDerivative p).natDegree = p.natDegree - 1 := by
  rw [monicDerivative, natDegree_C_mul (inv_ne_zero (by exact_mod_cast hn)),
    natDegree_derivative]






end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (p : Polynomial ℂ) (hp : p.Monic)
    (n : ℕ) (hdeg : p.natDegree = n+3) (hcenter : p.roots.sum = 0) :
    (n+3 : ℂ) * ((monicDerivative p).roots.map fun z => z^2).sum =
      (n+1 : ℂ) * (p.roots.map fun z => z^2).sum := by
  have hn : p.natDegree ≠ 0 := by omega
  have hnC : (n+3 : ℂ) ≠ 0 := by exact_mod_cast (show n+3 ≠ 0 by omega)
  have hq := monicDerivative_monic p hp hn
  have hqd : (monicDerivative p).natDegree = n+2 := by
    rw [monicDerivative_natDegree p hn, hdeg]; omega
  rw [polynomial_second_newton p hp (by omega),
    polynomial_second_newton (monicDerivative p) hq (by omega),
    monicDerivative_centered p hp n hdeg hcenter, hcenter, hqd, hdeg]
  simp only [zero_pow (by decide : 2 ≠ 0), zero_sub,
    show n+2-2=n by omega, show n+3-2=n+1 by omega,
    monicDerivative, coeff_C_mul, coeff_derivative, hdeg, Nat.cast_add, Nat.cast_ofNat]
  field_simp
