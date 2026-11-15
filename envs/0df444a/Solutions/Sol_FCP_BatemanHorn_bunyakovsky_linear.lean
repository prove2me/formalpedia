-- Prove2me | solution 1 for FCP.BatemanHorn.bunyakovsky_linear
-- status  : ACCEPTED   (prove)
-- author  : @Himan
-- created : 2026-11-15T03:59:26.945604+00:00
-- url     : https://prove2.me/submissions/da0c8d70-0d87-4073-9c9d-afc2d349ef11

import Mathlib
import Definitions.Def_FCP_BatemanHorn

open Polynomial FCP.BatemanHorn

theorem solution (f : ℤ[X]) (h_bunyakovsky : BunyakovskyCondition f)
    (h_deg : f.natDegree = 1) :
    {n : ℕ | (f.eval (n : ℤ)).natAbs.Prime}.Infinite := by
  obtain ⟨hlc, -, hirr⟩ := h_bunyakovsky
  -- write f = a X + b
  have hf : f = C (f.coeff 1) * X + C (f.coeff 0) :=
    Polynomial.eq_X_add_C_of_natDegree_le_one h_deg.le
  set a : ℤ := f.coeff 1 with ha
  set b : ℤ := f.coeff 0 with hb
  have ha_pos : 0 < a := by
    have : f.leadingCoeff = a := by rw [Polynomial.leadingCoeff, h_deg]
    rwa [this] at hlc
  have heval : ∀ n : ℤ, f.eval n = a * n + b := by
    intro n; rw [hf]; simp
  -- irreducible of positive degree ⇒ primitive ⇒ gcd(a, b) = 1
  have hprim : f.IsPrimitive := hirr.isPrimitive (by omega)
  have hcop : IsCoprime a b := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have hdvd : C ((Int.gcd a b : ℕ) : ℤ) ∣ f := by
      obtain ⟨a', ha'⟩ := Int.gcd_dvd_left a b
      obtain ⟨b', hb'⟩ := Int.gcd_dvd_right a b
      refine ⟨C a' * X + C b', ?_⟩
      rw [hf, mul_add, ← mul_assoc, ← C_mul, ← C_mul, ← ha', ← hb']
    have hu := hprim _ hdvd
    have := Int.isUnit_iff_natAbs_eq.mp hu
    simpa using this
  -- the modulus
  obtain ⟨q, hq⟩ : ∃ q : ℕ, (q : ℤ) = a := ⟨a.toNat, Int.toNat_of_nonneg ha_pos.le⟩
  have hq_pos : 0 < q := by exact_mod_cast hq ▸ ha_pos
  have : NeZero q := ⟨hq_pos.ne'⟩
  have hunit : IsUnit ((b : ℤ) : ZMod q) := by
    obtain ⟨u, v, huv⟩ := hcop
    have ha0 : ((a : ℤ) : ZMod q) = 0 := by rw [← hq]; simp
    have h1 := congrArg (Int.cast : ℤ → ZMod q) huv
    push_cast at h1
    rw [ha0, mul_zero, zero_add, mul_comm] at h1
    exact isUnit_iff_exists_inv.mpr ⟨_, h1⟩
  refine Set.infinite_of_forall_exists_gt fun N => ?_
  obtain ⟨p, hp_gt, hp, hpmod⟩ :=
    Nat.forall_exists_prime_gt_and_eq_mod hunit (q * N + b.natAbs)
  have hdiv : (q : ℤ) ∣ (p : ℤ) - b := by
    have : (((p : ℤ) - b : ℤ) : ZMod q) = 0 := by
      push_cast; rw [hpmod]; simp
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp this
  obtain ⟨k, hk⟩ := hdiv
  rw [hq] at hk
  have hk_gt : (N : ℤ) < k := by
    have h1 : ((q * N + b.natAbs : ℕ) : ℤ) < p := by exact_mod_cast hp_gt
    push_cast at h1
    rw [hq] at h1
    have h2 : b ≤ |b| := le_abs_self b
    have h3 : a * N < a * k := by rw [← hk]; linarith
    exact lt_of_mul_lt_mul_left h3 ha_pos.le
  refine ⟨k.toNat, ?_, ?_⟩
  · have hk0 : 0 ≤ k := le_trans (Int.natCast_nonneg N) hk_gt.le
    simp only [Set.mem_ofPred_eq]
    rw [Int.toNat_of_nonneg hk0, heval, ← hk]
    simpa using hp
  · have hk0 : 0 ≤ k := le_trans (Int.natCast_nonneg N) hk_gt.le
    have : ((N : ℤ)) < (k.toNat : ℤ) := by rwa [Int.toNat_of_nonneg hk0]
    exact_mod_cast this
