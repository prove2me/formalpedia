-- Prove2me | solution 1 for CerednikDrinfeld.CosetGraph.exists_nrd_mul_pow_eq_pow_of_mem_awayUnits
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:05.340288+00:00
-- url     : https://prove2.me/submissions/fc9ea47c-0018-58aa-b077-b3eb9ba184af

import Mathlib
import Definitions.Def_QuaternionAlgebra_Order
import Definitions.Def_QuaternionAlgebra_ReducedNorm
import Definitions.Def_CerednikDrinfeld_CosetGraphAtPrime
import Theorems.Thm_CerednikDrinfeld_CosetGraph_padicValRat_nrd_eq_zero_of_mem_awayUnits
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_CerednikDrinfeld_CosetGraph_exists_nrd_mul_pow_eq_pow_of_mem_awayUnits

set_option autoImplicit false

open scoped TensorProduct Quaternion NumberField
open IsDedekindDomain NumberField QuaternionAlgebra CerednikDrinfeld

namespace PenRt1NormAwayUnit

theorem nrd_mul {a b : ℚ} (x y : ℍ[ℚ, a, b]) : nrd (x * y) = nrd x * nrd y := by
  simp only [nrd, QuaternionAlgebra.re_mul, QuaternionAlgebra.imI_mul, QuaternionAlgebra.imJ_mul,
    QuaternionAlgebra.imK_mul]
  ring

theorem nrd_ne_zero_of_unit {a b : ℚ} (γ : (ℍ[ℚ, a, b])ˣ) : nrd ((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) ≠ 0 := by
  intro h
  have h1 : nrd (((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((γ⁻¹ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b])) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one, nrd_one]
  rw [nrd_mul, h, zero_mul] at h1
  exact zero_ne_one h1

theorem exists_mul_pow_eq_of_forall_padicValRat_eq_zero (r : ℕ) [hr : Fact r.Prime] (q : ℚ) (hq : q ≠ 0)
    (h : ∀ p : ℕ, p.Prime → p ≠ r → padicValRat p q = 0) :
    ∃ i j : ℕ, q * (r : ℚ) ^ i = (r : ℚ) ^ j ∨ q * (r : ℚ) ^ i = -((r : ℚ) ^ j) := by
  set n : ℕ := q.num.natAbs with hn
  set d : ℕ := q.den with hd
  have hn0 : n ≠ 0 := by
    simp only [hn, ne_eq, Int.natAbs_eq_zero]; exact Rat.num_ne_zero.mpr hq
  have hd0 : d ≠ 0 := q.den_ne_zero
  have hcop : n.Coprime d := q.reduced

  have key : ∀ p : ℕ, p.Prime → p ≠ r → ¬ p ∣ n ∧ ¬ p ∣ d := by
    intro p hp hpr
    haveI : Fact p.Prime := ⟨hp⟩
    have hv : ((padicValNat p n : ℕ) : ℤ) = ((padicValNat p d : ℕ) : ℤ) := by
      have := h p hp hpr
      simp only [padicValRat, padicValInt] at this
      linarith
    have hv' : padicValNat p n = padicValNat p d := by exact_mod_cast hv
    have hp1 : p ≠ 1 := hp.ne_one
    constructor
    · intro hpn
      have h1 : 1 ≤ padicValNat p n := one_le_padicValNat_of_dvd hn0 hpn
      have hpd : p ∣ d := dvd_of_one_le_padicValNat (hv' ▸ h1)
      exact hp1 (Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpn hpd))
    · intro hpd
      have h1 : 1 ≤ padicValNat p d := one_le_padicValNat_of_dvd hd0 hpd
      have hpn : p ∣ n := dvd_of_one_le_padicValNat (hv'.symm ▸ h1)
      exact hp1 (Nat.eq_one_of_dvd_one (hcop.gcd_eq_one ▸ Nat.dvd_gcd hpn hpd))
  obtain ⟨α, hα⟩ : ∃ α : ℕ, n = r ^ α :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hn0 (fun {p} hp hpn => by
      by_contra hpr; exact (key p hp hpr).1 hpn)⟩
  obtain ⟨β, hβ⟩ : ∃ β : ℕ, d = r ^ β :=
    ⟨_, Nat.eq_prime_pow_of_unique_prime_dvd hd0 (fun {p} hp hpd => by
      by_contra hpr; exact (key p hp hpr).2 hpd)⟩
  refine ⟨β, α, ?_⟩
  have hqd : q * (r : ℚ) ^ β = (q.num : ℚ) := by
    rw [← Rat.mul_den_eq_num, ← hd, hβ]; push_cast; rfl
  rcases Int.natAbs_eq q.num with hpos | hneg
  · left
    rw [hqd, hpos, ← hn, hα]; push_cast; rfl
  · right
    rw [hqd, hneg, ← hn, hα]; push_cast; rfl

end PenRt1NormAwayUnit

open PenRt1NormAwayUnit in
theorem solution
    {a b : ℚ} (R : Submodule ℤ ℍ[ℚ, a, b]) (hR : IsOrder R)
    (r : ℕ) [Fact r.Prime] (v : HeightOneSpectrum (𝓞 ℚ)) (hv : ((r : ℕ) : 𝓞 ℚ) ∈ v.asIdeal)
    (γ : (ℍ[ℚ, a, b])ˣ) (hγ : γ ∈ CerednikDrinfeld.CosetGraph.awayUnits R v) :
    ∃ i j : ℕ, nrd ((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((r : ℚ) ^ i) = (r : ℚ) ^ j ∨
      nrd ((γ : (ℍ[ℚ, a, b])ˣ) : ℍ[ℚ, a, b]) * ((r : ℚ) ^ i) = -((r : ℚ) ^ j) := by
  have hval := (CerednikDrinfeld.CosetGraph.padicValRat_nrd_eq_zero_of_mem_awayUnits R hR r v hv).1 γ hγ
  exact exists_mul_pow_eq_of_forall_padicValRat_eq_zero r _ (nrd_ne_zero_of_unit γ) hval

end S_CerednikDrinfeld_CosetGraph_exists_nrd_mul_pow_eq_pow_of_mem_awayUnits
end P2MW
export P2MW.S_CerednikDrinfeld_CosetGraph_exists_nrd_mul_pow_eq_pow_of_mem_awayUnits (solution)
