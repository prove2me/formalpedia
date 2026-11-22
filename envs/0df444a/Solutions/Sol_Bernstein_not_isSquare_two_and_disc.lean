-- Prove2me | solution 1 for Bernstein.not_isSquare_two_and_disc
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-11-22T17:36:33.026412+00:00
-- url     : https://prove2.me/submissions/21faccca-1a6e-42f8-931f-54a64cf927ee

import Mathlib
import Definitions.Def_Curve25519Bernstein
import Theorems.Thm_Bernstein_prime_p25519

set_option autoImplicit false

namespace Bernstein.Arith.NS

/-- Square-and-multiply worker (as in spitters/CatCrypt-core, `PrattCertificate.lean`, MIT). -/
def powModGo (m : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ
  | 0,      _,    _, acc => acc
  | fuel+1, base, e, acc =>
      if e = 0 then acc else
        let acc' := if e % 2 = 1 then (acc * base) % m else acc
        powModGo m fuel ((base * base) % m) (e / 2) acc'

/-- Binary modular exponentiation `a ^ k % n`. -/
def powMod (a k n : ℕ) : ℕ := powModGo n k (a % n) k (1 % n)

theorem powModGo_cast (m : ℕ) :
    ∀ (fuel base e acc : ℕ), e < 2 ^ fuel →
      ((powModGo m fuel base e acc : ℕ) : ZMod m) = (acc : ZMod m) * (base : ZMod m) ^ e := by
  intro fuel
  induction fuel with
  | zero =>
      intro base e acc he
      have he0 : e = 0 := by simpa using he
      subst he0; simp [powModGo]
  | succ fuel ih =>
      intro base e acc he
      rw [powModGo]
      by_cases h0 : e = 0
      · subst h0; simp
      · simp only [h0, ite_false]
        have hlt : e / 2 < 2 ^ fuel := by
          have : (2 : ℕ) ^ (fuel + 1) = 2 * 2 ^ fuel := by rw [pow_succ]; ring
          omega
        rw [ih _ _ _ hlt]
        have hbase : (((base * base) % m : ℕ) : ZMod m) = (base : ZMod m) ^ 2 := by
          rw [ZMod.natCast_mod]; push_cast; ring
        rw [hbase]
        have hacc : (((if e % 2 = 1 then (acc * base) % m else acc) : ℕ) : ZMod m)
              = (acc : ZMod m) * (base : ZMod m) ^ (e % 2) := by
          by_cases h1 : e % 2 = 1
          · simp only [h1, ite_true]; rw [ZMod.natCast_mod]; push_cast; ring
          · have : e % 2 = 0 := by omega
            simp [this]
        rw [hacc, ← pow_mul, mul_assoc, ← pow_add]
        congr 2
        omega

theorem powMod_cast (a k n : ℕ) [NeZero n] :
    ((powMod a k n : ℕ) : ZMod n) = (a : ZMod n) ^ k := by
  rw [powMod, powModGo_cast n k (a % n) k (1 % n) Nat.lt_two_pow_self,
    ZMod.natCast_mod, ZMod.natCast_mod, Nat.cast_one, one_mul]

/-- The kernel computation: `(486662^2 - 4)^((p-1)/2) ≡ p - 1 (mod p)`. -/
theorem powMod_disc :
    powMod (486662 ^ 2 - 4) (p25519 / 2) p25519 = p25519 - 1 := by
  decide +kernel

theorem p25519_mod_eight : p25519 % 8 = 5 := by decide +kernel

theorem not_isSquare_two_and_disc_dev :
    ¬ IsSquare (2 : ZMod p25519) ∧
    IsField (AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C (2 : ZMod p25519))) ∧
    ¬ IsSquare ((A25519 : ZMod p25519) ^ 2 - 4) := by
  have : Fact p25519.Prime := ⟨Bernstein.prime_p25519⟩
  have h2 : ¬ IsSquare (2 : ZMod p25519) := by
    rw [ZMod.exists_sq_eq_two_iff (by decide +kernel), p25519_mod_eight]
    decide
  refine ⟨h2, ?_, ?_⟩
  · have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (2 : ZMod p25519)) := by
      apply X_pow_sub_C_irreducible_of_prime Nat.prime_two
      intro b hb
      exact h2 ⟨b, by rw [← hb]; ring⟩
    have : Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (2 : ZMod p25519))) := ⟨hirr⟩
    exact Field.toIsField _
  · have hcast : ((A25519 : ZMod p25519) ^ 2 - 4) = ((486662 ^ 2 - 4 : ℕ) : ZMod p25519) := by
      simp [A25519]
      norm_num
    rw [hcast]
    have hne : ((486662 ^ 2 - 4 : ℕ) : ZMod p25519) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      decide +kernel
    rw [ZMod.euler_criterion p25519 hne, ← powMod_cast, powMod_disc]
    have hp1 : 1 ≤ p25519 := by decide +kernel
    rw [Nat.cast_sub hp1, ZMod.natCast_self, Nat.cast_one, zero_sub]
    intro h
    have h' : (2 : ZMod p25519) = 0 := by linear_combination -h
    exact h2 ⟨0, by rw [h']; ring⟩

end Bernstein.Arith.NS

theorem solution : type_of% @Bernstein.Arith.NS.not_isSquare_two_and_disc_dev := @Bernstein.Arith.NS.not_isSquare_two_and_disc_dev
