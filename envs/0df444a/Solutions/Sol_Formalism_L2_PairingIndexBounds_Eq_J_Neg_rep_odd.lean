-- Prove2me | solution 1 for Formalism.L2.PairingIndexBounds.Eq.J.Neg.rep_odd
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T21:25:57.951576+00:00
-- url     : https://prove2.me/submissions/124946b3-bf4c-49aa-8886-fcba5bfb62f7

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_PairingIndexBounds_SplitPairEquations_IntegralSquareRoots_HenselQuad
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_hensel_quad
import Theorems.Thm_Formalism_L2_PairingIndexBounds_Eq_J_Neg_norm_unit
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open Polynomial
namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg
private theorem padic_norm_lt_norm_sq_of_dvd_of_not_dvd (p : ℕ) [Fact p.Prime] (u v : ℤ) (hu : (p : ℤ) ∣ u)
    (hv : ¬ (p : ℤ) ∣ v) : ‖(u : ℤ_[p])‖ < ‖(v : ℤ_[p])‖ ^ 2 := by
  rw [norm_unit p v hv, one_pow]
  exact (PadicInt.norm_int_lt_one_iff_dvd (p := p) (k := u)).2 hu
end Formalism.L2.PairingIndexBounds.Eq.J.Neg
end

set_option autoImplicit false
open Polynomial
open Formalism Formalism.L2 Formalism.L2.PairingIndexBounds Formalism.L2.PairingIndexBounds.Eq Formalism.L2.PairingIndexBounds.Eq.J Formalism.L2.PairingIndexBounds.Eq.J.Neg
namespace Formalism.L2.PairingIndexBounds.Eq.J.Neg
theorem _root_.solution (p : ℕ) [hp : Fact p.Prime] (hp2 : p ≠ 2) (c : ℕ) (hc : ¬ p ∣ c) :
    ∃ x y : ℤ_[p], x ^ 2 + (c : ℤ_[p]) * y ^ 2 = -1 := by
  have : NeZero p := ⟨hp.out.ne_zero⟩
  have hcp : (c : ZMod p) ≠ 0 := fun h => hc ((CharP.cast_eq_zero_iff (ZMod p) p c).1 h)
  have hodd : Fintype.card (ZMod p) % 2 = 1 := by
    rw [ZMod.card]; exact Nat.odd_iff.1 (hp.out.odd_of_ne_two hp2)
  obtain ⟨u, v, huv⟩ := FiniteField.exists_root_sum_quadratic
    (f := X ^ 2 + C (1 : ZMod p)) (g := C (c : ZMod p) * X ^ 2)
    (by simpa using degree_X_pow_add_C (R := ZMod p) (n := 2) (by norm_num) 1)
    (by simpa using degree_C_mul_X_pow 2 hcp) hodd
  obtain ⟨x₀, rfl⟩ := ZMod.intCast_surjective u
  obtain ⟨y₀, rfl⟩ := ZMod.intCast_surjective v
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have h2 : ¬ (p : ℤ) ∣ 2 := by
    intro h
    have h' : p ∣ 2 := by exact_mod_cast h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h')
  have hcz : ¬ (p : ℤ) ∣ (c : ℤ) := by exact_mod_cast hc
  have hdiv : (p : ℤ) ∣ x₀ ^ 2 + (c : ℤ) * y₀ ^ 2 + 1 := by
    rw [← CharP.intCast_eq_zero_iff (ZMod p) p]
    simp only [eval_add, eval_pow, eval_X, eval_C, eval_mul] at huv
    push_cast
    linear_combination huv
  by_cases hx : (p : ℤ) ∣ x₀
  · have hy : ¬ (p : ℤ) ∣ y₀ := by
      intro hy
      have h1 : (p : ℤ) ∣ 1 := by
        have e : (1 : ℤ) = (x₀ ^ 2 + (c : ℤ) * y₀ ^ 2 + 1) - (x₀ ^ 2 + (c : ℤ) * y₀ ^ 2) := by ring
        rw [e]
        exact dvd_sub hdiv (dvd_add (dvd_pow hx two_ne_zero)
          (dvd_mul_of_dvd_right (dvd_pow hy two_ne_zero) (c : ℤ)))
      exact hpz.not_dvd_one h1
    obtain ⟨z, hz⟩ := hensel_quad p c (x₀ ^ 2 + 1) y₀
      (padic_norm_lt_norm_sq_of_dvd_of_not_dvd p _ _ (by convert hdiv using 1; ring)
        (fun h => (hpz.dvd_or_dvd h).elim (fun h => (hpz.dvd_or_dvd h).elim h2 hcz) hy))
    exact ⟨x₀, z, by push_cast at hz; linear_combination hz⟩
  · obtain ⟨z, hz⟩ := hensel_quad p 1 (c * y₀ ^ 2 + 1) x₀
      (padic_norm_lt_norm_sq_of_dvd_of_not_dvd p _ _ (by convert hdiv using 1; ring)
        (fun h => (hpz.dvd_or_dvd h).elim
          (fun h => (hpz.dvd_or_dvd h).elim h2 hpz.not_dvd_one) hx))
    exact ⟨z, y₀, by push_cast at hz; linear_combination hz⟩
end Formalism.L2.PairingIndexBounds.Eq.J.Neg
