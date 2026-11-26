-- Prove2me | solution 1 for FixedOrderFactor.not_pow_succ_dvd_sq_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:03:45.828392+00:00
-- url     : https://prove2.me/submissions/fd8d1944-da83-4e10-902d-ee1bdfa8d6e4

module
public import Definitions.Def_FixedOrderFactor_Local
public import Definitions.Def_FixedOrderFactor_Bias

set_option autoImplicit true
@[expose] public section
public section
open Finset Real Complex
open FixedOrderFactor
namespace FixedOrderFactor
theorem _root_.solution {r x : ℕ} (hr : 0 < r)
    (hsq : x ^ 2 % (2 * r) = (1 + r) % (2 * r))
    (hdvd : ((2 ^ (r.factorization 2 + 1) : ℕ) : ℤ) ∣ (x : ℤ) ^ 2 - 1) : False := by
  set k := r.factorization 2
  have hk : 2 ^ k ∣ r := Nat.ordProj_dvd r 2
  have hP : 2 ^ (k + 1) ∣ 2 * r := by rw [pow_succ, mul_comm]; exact Nat.mul_dvd_mul_left 2 hk
  have hmod : ((2 * r : ℕ) : ℤ) ∣ ((1 + r : ℕ) : ℤ) - ((x ^ 2 : ℕ) : ℤ) :=
    (Nat.modEq_iff_dvd).1 hsq
  have h1 : ((2 ^ (k + 1) : ℕ) : ℤ) ∣ ((1 + r : ℕ) : ℤ) - ((x ^ 2 : ℕ) : ℤ) :=
    (Int.natCast_dvd_natCast.2 hP).trans hmod
  have h2 : ((2 ^ (k + 1) : ℕ) : ℤ) ∣ (r : ℤ) := by
    have hsum := dvd_add h1 hdvd
    have heq : (((1 + r : ℕ) : ℤ) - ((x ^ 2 : ℕ) : ℤ)) + ((x : ℤ) ^ 2 - 1) = (r : ℤ) := by
      push_cast; ring
    rwa [heq] at hsum
  exact Nat.pow_succ_factorization_not_dvd hr.ne' Nat.prime_two (Int.natCast_dvd_natCast.1 h2)
end FixedOrderFactor
