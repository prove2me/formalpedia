-- Prove2me | solution 1 for Erdos287.short_type_ii_nonzero_determinant_fiber_bound
-- status  : ACCEPTED   (prove)
-- author  : @immiq
-- created : 2026-11-26T21:23:22.605698+00:00
-- url     : https://prove2.me/submissions/b25de79d-8aec-425a-99a9-1ad4280c62e0

import Mathlib

open Finset

set_option autoImplicit false

private theorem dvd_natAbs {k : ℕ} {z : ℤ} (h : (k : ℤ) ∣ z) :
    k ∣ z.natAbs := by
  obtain ⟨v, hv⟩ := h
  refine ⟨v.natAbs, ?_⟩
  rw [hv, Int.natAbs_mul, Int.natAbs_natCast]

/-- Bound the nonzero-difference determinant fiber by two divisor counts. -/
theorem solution (a b c D C : ℕ) (u : ℤ) (ha : 0 < a) (hu : u ≠ 0)
    (hbc : b ≠ c) (hD : ((a : ℤ) * u).natAbs ≤ D)
    (hC : ∀ d : ℕ, 0 < d → d ≤ D → d.divisors.card ≤ C)
    (T : Finset (ℕ × ℕ × ℤ))
    (hT : ∀ t ∈ T, 0 < t.1 ∧ 0 < t.2.1 ∧ t.1 ≠ b ∧ t.1.Coprime b ∧
      ((a : ℤ) * ((b : ℤ) - (t.1 : ℤ)) * u).natAbs ≤ D ∧
      (a : ℤ) * ((b : ℤ) - (t.1 : ℤ)) * u =
        (t.1 : ℤ) * (t.2.1 : ℤ) * ((b : ℤ) - (c : ℤ)) * t.2.2) :
    T.card ≤ C * C := by
  let value (k : ℕ) := (a : ℤ) * ((b : ℤ) - (k : ℤ)) * u
  have ha' : (a : ℤ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbc' : (b : ℤ) - (c : ℤ) ≠ 0 := by
    apply sub_ne_zero.mpr
    exact_mod_cast hbc
  have hau : 0 < ((a : ℤ) * u).natAbs := Int.natAbs_pos.mpr (mul_ne_zero ha' hu)
  have hvalue (k : ℕ) (hkb : k ≠ b) : 0 < (value k).natAbs := by
    apply Int.natAbs_pos.mpr
    have hdiff : (b : ℤ) - (k : ℤ) ≠ 0 := by
      apply sub_ne_zero.mpr
      exact_mod_cast hkb.symm
    exact mul_ne_zero (mul_ne_zero ha' hdiff) hu
  have hkdiv (t : ℕ × ℕ × ℤ) (ht : t ∈ T) : t.1 ∣ ((a : ℤ) * u).natAbs := by
    obtain ⟨_, _, _, hcop, _, heq⟩ := hT t ht
    have hdiv : (t.1 : ℤ) ∣ (a : ℤ) * ((b : ℤ) - (t.1 : ℤ)) * u :=
      ⟨(t.2.1 : ℤ) * ((b : ℤ) - (c : ℤ)) * t.2.2, heq.trans (by ring)⟩
    have hprod : (t.1 : ℤ) ∣ ((a : ℤ) * u) * (b : ℤ) := by
      have he : ((a : ℤ) * u) * (b : ℤ) =
          (a : ℤ) * ((b : ℤ) - (t.1 : ℤ)) * u + (t.1 : ℤ) * ((a : ℤ) * u) := by
        ring
      rw [he]
      exact dvd_add hdiv (dvd_mul_right (t.1 : ℤ) ((a : ℤ) * u))
    exact dvd_natAbs (hcop.isCoprime.dvd_of_dvd_mul_right hprod)
  let K := T.image Prod.fst
  have hK : K.card ≤ C := by
    refine (card_le_card ?_).trans (hC _ hau hD)
    intro k hk
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hk
    exact Nat.mem_divisors.mpr ⟨hkdiv t ht, hau.ne'⟩
  have hfiber (k : ℕ) (hk : k ∈ K) : (T.filter (fun t => t.1 = k)).card ≤ C := by
    obtain ⟨t, ht, rfl⟩ := mem_image.mp hk
    obtain ⟨_, _, htb, _, hbound, _⟩ := hT t ht
    have hpos := hvalue t.1 htb
    refine (card_le_card_of_injOn (fun z : ℕ × ℕ × ℤ => z.2.1) ?_ ?_).trans
      (hC _ hpos hbound)
    · intro z hz
      obtain ⟨hz, hzt⟩ := mem_filter.mp hz
      obtain ⟨_, _, _, _, _, heq⟩ := hT z hz
      apply Nat.mem_divisors.mpr
      refine ⟨dvd_natAbs ?_, hpos.ne'⟩
      refine ⟨(z.1 : ℤ) * ((b : ℤ) - (c : ℤ)) * z.2.2, ?_⟩
      rw [← hzt]
      exact heq.trans (by ring)
    · rintro ⟨k, s, v⟩ hx ⟨k', s', v'⟩ hy hs
      change s = s' at hs
      subst s'
      obtain ⟨hx, hk⟩ := mem_filter.mp hx
      obtain ⟨hy, hk'⟩ := mem_filter.mp hy
      change k = t.1 at hk
      change k' = t.1 at hk'
      subst k'
      subst k
      obtain ⟨hk0, hs0, _, _, _, hxEq⟩ := hT (t.1, s, v) hx
      obtain ⟨_, _, _, _, _, hyEq⟩ := hT (t.1, s, v') hy
      have hk0' : (t.1 : ℤ) ≠ 0 := by exact_mod_cast hk0.ne'
      have hs0' : (s : ℤ) ≠ 0 := by exact_mod_cast hs0.ne'
      have hv : v = v' :=
        mul_left_cancel₀ (mul_ne_zero (mul_ne_zero hk0' hs0') hbc') (hxEq.symm.trans hyEq)
      exact congrArg (fun w => (t.1, s, w)) hv
  calc
    T.card = ∑ k ∈ K, (T.filter (fun t => t.1 = k)).card :=
      card_eq_sum_card_image Prod.fst T
    _ ≤ ∑ _k ∈ K, C := sum_le_sum hfiber
    _ = K.card * C := by simp
    _ ≤ C * C := Nat.mul_le_mul_right C hK

