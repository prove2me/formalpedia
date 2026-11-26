-- Prove2me | solution 1 for Erdos287.type_iii_common_residue_gcd
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T04:42:50.743844+00:00
-- url     : https://prove2.me/submissions/0cec558b-40dc-4be7-9367-11bf6e0d0f44

import Mathlib

set_option autoImplicit false

/-- The gcd arising in a correlation can be evaluated without the common
unit residue, even when the residue itself is unbounded. -/
theorem solution (m a n₁ n₂ ρ₁ ρ₂ b₁ b₂ : ℤ)
    (h₁ : ρ₁ * n₁ ≡ a [ZMOD m]) (h₂ : ρ₂ * n₂ ≡ a [ZMOD m])
    (ha : IsCoprime m a) (hn : IsCoprime m (n₁ * n₂)) :
    Int.gcd (ρ₁ * b₂ - ρ₂ * b₁) m = Int.gcd (n₂ * b₂ - n₁ * b₁) m := by
  let L := ρ₁ * b₂ - ρ₂ * b₁
  let R := n₂ * b₂ - n₁ * b₁
  have hmod : L * (n₁ * n₂) ≡ a * R [ZMOD m] := by
    have h := (h₁.mul_right (n₂ * b₂)).sub (h₂.mul_right (n₁ * b₁))
    convert h using 1 <;> dsimp [L, R] <;> ring
  have hdiv (d : ℤ) (hd : d ∣ m) : d ∣ L ↔ d ∣ R := by
    constructor
    · intro hL
      exact (ha.of_isCoprime_of_dvd_left hd).dvd_of_dvd_mul_left
        ((hmod.of_dvd hd).dvd_iff.mp (hL.mul_right _))
    · intro hR
      exact (hn.of_isCoprime_of_dvd_left hd).dvd_of_dvd_mul_right
        ((hmod.of_dvd hd).dvd_iff.mpr (hR.mul_left _))
  apply Nat.dvd_antisymm
  · apply Int.natCast_dvd_natCast.mp
    exact Int.dvd_coe_gcd
      ((hdiv _ (Int.gcd_dvd_right L m)).mp (Int.gcd_dvd_left L m))
      (Int.gcd_dvd_right L m)
  · apply Int.natCast_dvd_natCast.mp
    exact Int.dvd_coe_gcd
      ((hdiv _ (Int.gcd_dvd_right R m)).mpr (Int.gcd_dvd_left R m))
      (Int.gcd_dvd_right R m)

