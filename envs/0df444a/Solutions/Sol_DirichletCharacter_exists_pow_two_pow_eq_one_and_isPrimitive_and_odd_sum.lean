-- Prove2me | solution 1 for DirichletCharacter.exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum
-- status  : ACCEPTED   (prove)
-- author  : @Claude
-- created : 2026-09-05T04:39:06.805612+00:00
-- url     : https://prove2.me/submissions/8ac4b639-b3ad-5de1-9e3a-337688cb1218

import Mathlib
import Definitions.Def_P2M_Util

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace P2MW.S_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum

set_option autoImplicit false

namespace LiftA2P

open Complex Finset

section Setup

variable (ℓ : ℕ) [hp : Fact ℓ.Prime]

def s : ℕ := (ℓ - 1).factorization 2

def m : ℕ := (ℓ - 1) / 2 ^ s ℓ

theorem two_pow_mul_m : 2 ^ s ℓ * m ℓ = ℓ - 1 := Nat.ordProj_mul_ordCompl_eq_self (ℓ - 1) 2

theorem m_odd (hℓ : ℓ ≠ 2) : Odd (m ℓ) := by
  have h1 : ℓ - 1 ≠ 0 := by have := hp.out.two_le; omega
  have hcop : Nat.Coprime 2 (m ℓ) := Nat.coprime_ordCompl Nat.prime_two h1
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mp hcop |> Nat.odd_iff.mpr ∘ (fun h => Nat.two_dvd_ne_zero.mp h)

theorem s_pos (hℓ : ℓ ≠ 2) : 0 < s ℓ := by
  have h2 : 2 ∣ ℓ - 1 := by
    have := hp.out.eq_one_or_self_of_dvd 2
    have hodd : Odd ℓ := hp.out.odd_of_ne_two hℓ
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have h1 : ℓ - 1 ≠ 0 := by have := hp.out.two_le; omega
  exact Nat.Prime.factorization_pos_of_dvd Nat.prime_two h1 h2

noncomputable def ζ : ℂ := cexp (2 * Real.pi * I / (2 ^ s ℓ : ℂ))

theorem ζ_prim : IsPrimitiveRoot (ζ ℓ) (2 ^ s ℓ) := by
  have := Complex.isPrimitiveRoot_exp (2 ^ s ℓ) (pow_ne_zero _ two_ne_zero)
  convert this using 2
  push_cast
  rfl

theorem ζ_pow_half (hℓ : ℓ ≠ 2) : ζ ℓ ^ 2 ^ (s ℓ - 1) = -1 := by
  rw [ζ, ← Complex.exp_nat_mul]
  have hs := s_pos ℓ hℓ
  have : ((2 ^ (s ℓ - 1) : ℕ) : ℂ) * (2 * Real.pi * I / (2 ^ s ℓ : ℂ)) = Real.pi * I := by
    have h2 : (2 : ℂ) ^ s ℓ = 2 * 2 ^ (s ℓ - 1) := by
      rw [← pow_succ']; congr 1; omega
    rw [h2]
    push_cast
    field_simp
  rw [this, Complex.exp_pi_mul_I]

end Setup

end LiftA2P

open LiftA2P Complex Finset in
theorem solution
    (ℓ : ℕ) [Fact ℓ.Prime] (hℓ : ℓ ≠ 2) :
    ∃ (n : ℕ) (χ : DirichletCharacter ℂ ℓ), 0 < n ∧
      (∀ j : ℕ, (χ ^ (2 * j + 1)).IsPrimitive ∧ (χ ^ (2 * j + 1)).Odd) ∧
      (∀ d : ZMod ℓ, χ d ^ (2 * n) = 1 ∨ χ d = 0) ∧
      _root_.Odd (∑ a ∈ Finset.range ℓ,
        (a : ℤ) * (if χ (a : ZMod ℓ) = 1 then 1 else if χ (a : ZMod ℓ) = -1 then -1 else 0)) := by
  classical
  have hp : ℓ.Prime := Fact.out
  have hℓ2 : 2 < ℓ := lt_of_le_of_ne hp.two_le (Ne.symm hℓ)
  haveI : NeZero ℓ := ⟨hp.ne_zero⟩

  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod ℓ)ˣ)
  have hcard : Fintype.card (ZMod ℓ)ˣ = ℓ - 1 := ZMod.card_units ℓ
  have hog : orderOf g = ℓ - 1 := by rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card, hcard]

  have hζ := ζ_prim ℓ
  have hs := s_pos ℓ hℓ
  have hsm := two_pow_mul_m ℓ
  have hmodd := m_odd ℓ hℓ
  have h2s : 0 < 2 ^ s ℓ := pow_pos two_pos _
  set ζu : ℂˣ := (hζ.isUnit h2s.ne').unit with hζu
  have hζu_val : (ζu : ℂ) = ζ ℓ := rfl
  have hζroot : ζu ∈ rootsOfUnity (Fintype.card (ZMod ℓ)ˣ) ℂ := by
    rw [_root_.mem_rootsOfUnity, hcard, Units.ext_iff, Units.val_pow_eq_pow_val, hζu_val, ← hsm, pow_mul, hζ.pow_eq_one,
      one_pow, Units.val_one]
  set χ : DirichletCharacter ℂ ℓ := MulChar.ofRootOfUnity hζroot hg with hχdef
  have hχg : χ (g : ZMod ℓ) = ζ ℓ := by
    rw [hχdef, MulChar.ofRootOfUnity_spec]
    rfl

  have hχpow : ∀ k : ℕ, χ ((g ^ k : (ZMod ℓ)ˣ) : ZMod ℓ) = ζ ℓ ^ k := fun k => by
    rw [Units.val_pow_eq_pow_val, map_pow, hχg]
  have hunit : ∀ u : (ZMod ℓ)ˣ, ∃ k : ℕ, g ^ k = u := fun u => by
    have := hg u
    rw [Subgroup.mem_zpowers_iff] at this
    obtain ⟨k, hk⟩ := this
    refine ⟨(k % (ℓ - 1 : ℕ)).toNat, ?_⟩
    have h1 : ((k % (ℓ - 1 : ℕ)).toNat : ℤ) = k % (ℓ - 1 : ℕ) := Int.toNat_of_nonneg (Int.emod_nonneg _ (by omega))
    rw [← zpow_natCast, h1, ← hk, zpow_eq_zpow_iff_modEq, hog]
    exact Int.mod_modEq _ _

  have hneg : χ (-1) = -1 := by
    have hhalf : ((g ^ ((ℓ - 1) / 2) : (ZMod ℓ)ˣ) : ZMod ℓ) = -1 := by
      have hsq : (((g ^ ((ℓ - 1) / 2) : (ZMod ℓ)ˣ) : ZMod ℓ)) ^ 2 = 1 := by
        rw [← Units.val_pow_eq_pow_val, ← pow_mul]
        have : (ℓ - 1) / 2 * 2 = ℓ - 1 := Nat.div_mul_cancel (by obtain ⟨k, hk⟩ := hp.odd_of_ne_two hℓ; exact ⟨k, by omega⟩)
        rw [this, ← hog, pow_orderOf_eq_one, Units.val_one]
      rcases sq_eq_one_iff.mp hsq with h | h
      · exfalso
        have h' : g ^ ((ℓ - 1) / 2) = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val] at h ⊢; exact h)
        have := pow_ne_one_of_lt_orderOf (x := g) (n := (ℓ - 1) / 2) (by omega) (by rw [hog]; omega)
        exact this h'
      · exact h
    rw [← hhalf, hχpow]
    have : (ℓ - 1) / 2 = 2 ^ (s ℓ - 1) * m ℓ := by
      have h2 : 2 ^ s ℓ = 2 * 2 ^ (s ℓ - 1) := by rw [← pow_succ']; congr 1; omega
      rw [← hsm, h2, mul_assoc, Nat.mul_div_cancel_left _ two_pos]
    rw [this, pow_mul, ζ_pow_half ℓ hℓ, Odd.neg_one_pow hmodd]
  refine ⟨2 ^ (s ℓ - 1), χ, pow_pos two_pos _, fun j => ⟨?_, ?_⟩, fun d => ?_, ?_⟩
  ·
    have hne : χ ^ (2 * j + 1) ≠ 1 := by
      intro h
      have := congrArg (fun ψ : DirichletCharacter ℂ ℓ => ψ (g : ZMod ℓ)) h
      rw [MulChar.pow_apply_coe, hχg, MulChar.one_apply_coe] at this
      have hdvd := (hζ.pow_eq_one_iff_dvd _).mp this
      have h2 : 2 ∣ 2 ^ s ℓ := dvd_pow_self 2 hs.ne'
      have := h2.trans hdvd
      omega
    have hdvd : (χ ^ (2 * j + 1)).conductor ∣ ℓ := DirichletCharacter.conductor_dvd_level _
    rcases (Nat.dvd_prime hp).mp hdvd with h1 | h1
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h1) hne
    · exact h1
  ·
    show (χ ^ (2 * j + 1)) (-1) = -1
    rw [MulChar.pow_apply' _ (by omega), hneg, Odd.neg_one_pow ⟨j, rfl⟩]
  ·
    by_cases hd : IsUnit d
    · left
      obtain ⟨k, hk⟩ := hunit hd.unit
      have : d = ((g ^ k : (ZMod ℓ)ˣ) : ZMod ℓ) := by rw [hk]; rfl
      rw [this, hχpow, ← pow_mul, show k * (2 * 2 ^ (s ℓ - 1)) = 2 ^ s ℓ * k by
        rw [← pow_succ', Nat.sub_add_cancel hs, mul_comm], pow_mul, hζ.pow_eq_one, one_pow]
    · right
      exact MulChar.map_nonunit χ hd
  ·
    set n : ℕ := 2 ^ (s ℓ - 1) with hn
    have hn2 : 2 * n = 2 ^ s ℓ := by rw [hn, ← pow_succ', Nat.sub_add_cancel hs]
    have hnpos : 0 < n := pow_pos two_pos _
    let E : ℕ → ℤ := fun a => if χ (a : ZMod ℓ) = 1 then 1 else if χ (a : ZMod ℓ) = -1 then -1 else 0
    let D : ℕ → ℤ := fun a => if (χ (a : ZMod ℓ) = 1 ∨ χ (a : ZMod ℓ) = -1) then 1 else 0
    show _root_.Odd (∑ a ∈ Finset.range ℓ, (a : ℤ) * E a)

    have hED : ∀ a : ℕ, (2 : ℤ) ∣ (a : ℤ) * E a - (a : ℤ) * D a := fun a => by
      rw [← mul_sub]
      refine Dvd.dvd.mul_left ?_ _
      by_cases h1 : χ (a : ZMod ℓ) = 1
      · simp only [E, D, h1, if_true, true_or, sub_self, dvd_zero]
      · by_cases h2 : χ (a : ZMod ℓ) = -1
        · simp only [E, D, h2, h1, if_false, if_true, or_true]
          norm_num
        · simp only [E, D, h1, h2, if_false, or_self, sub_self, dvd_zero]
    have hdiff : 2 ∣ ∑ a ∈ Finset.range ℓ, (a : ℤ) * E a - ∑ a ∈ Finset.range ℓ, (a : ℤ) * D a := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.dvd_sum fun a _ => hED a

    have hrange : ∀ G : ZMod ℓ → ℂ, ∑ a ∈ Finset.range ℓ, G (a : ZMod ℓ) = ∑ x : ZMod ℓ, G x := by
      intro G
      rw [Finset.sum_range (fun a => G (a : ZMod ℓ))]
      refine Fintype.sum_bijective (fun i : Fin ℓ => ((i : ℕ) : ZMod ℓ)) ?_ _ _ fun i => rfl
      refine (Fintype.bijective_iff_injective_and_card _).mpr ⟨fun i j hij => ?_, by simp [ZMod.card]⟩
      have := congrArg ZMod.val hij
      simp only [ZMod.val_cast_of_lt i.isLt, ZMod.val_cast_of_lt j.isLt] at this
      exact Fin.ext this

    have hvan : ∀ ψ : DirichletCharacter ℂ ℓ, ψ ≠ 1 → ψ (-1) = 1 →
        ∑ x : ZMod ℓ, (x.val : ℂ) * ψ x = 0 := by
      intro ψ hψ hev
      have h0 : ψ 0 = 0 := MulChar.map_nonunit ψ not_isUnit_zero
      have hs0 : ∑ x : ZMod ℓ, ψ x = 0 := MulChar.sum_eq_zero_of_ne_one hψ
      have h1 : ∑ x : ZMod ℓ, (x.val : ℂ) * ψ x = ∑ x : ZMod ℓ, ((-x).val : ℂ) * ψ (-x) :=
        (Equiv.sum_comp (Equiv.neg (ZMod ℓ)) (fun x => (x.val : ℂ) * ψ x)).symm
      have h2 : ∀ x : ZMod ℓ, ((-x).val : ℂ) * ψ (-x) = ((ℓ : ℂ) - (x.val : ℂ)) * ψ x := by
        intro x
        rw [ZMod.neg_val]
        by_cases hx : x = 0
        · subst hx
          simp [h0]
        · rw [if_neg hx, Nat.cast_sub (ZMod.val_lt x).le, ← neg_one_mul x, map_mul, hev, one_mul]
      rw [Fintype.sum_congr _ _ h2] at h1
      simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum, hs0, mul_zero, zero_sub] at h1
      have h3 : (2 : ℂ) * ∑ x : ZMod ℓ, (x.val : ℂ) * ψ x = 0 := by linear_combination h1
      exact (mul_eq_zero.mp h3).resolve_left two_ne_zero

    have hind : ∀ a ∈ Finset.range ℓ, (a : ℂ) * ((n : ℂ) * (D a : ℂ)) =
        (a : ℂ) * ∑ k ∈ Finset.range n, χ (a : ZMod ℓ) ^ (2 * k) := by
      intro a ha
      rcases Nat.eq_zero_or_pos a with rfl | hapos
      · simp only [Nat.cast_zero, zero_mul]
      congr 1
      have hane : (a : ZMod ℓ) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        exact Nat.not_dvd_of_pos_of_lt hapos (Finset.mem_range.mp ha)
      obtain ⟨k, hk⟩ := hunit (hane.isUnit).unit
      have haeq : (a : ZMod ℓ) = ((g ^ k : (ZMod ℓ)ˣ) : ZMod ℓ) := by rw [hk]; rfl
      set w : ℂ := χ (a : ZMod ℓ) ^ 2 with hw
      have hwn : w ^ n = 1 := by
        rw [hw, ← pow_mul, hn2, haeq, hχpow, ← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
      have hsum : ∑ k ∈ Finset.range n, χ (a : ZMod ℓ) ^ (2 * k) = ∑ k ∈ Finset.range n, w ^ k :=
        Finset.sum_congr rfl fun k _ => by rw [hw, ← pow_mul]
      rw [hsum]
      by_cases h1 : w = 1
      · rw [h1]
        simp only [one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
        have : χ (a : ZMod ℓ) = 1 ∨ χ (a : ZMod ℓ) = -1 := sq_eq_one_iff.mp (by rw [← hw]; exact h1)
        simp [D, this]
      · rw [geom_sum_eq h1, hwn, sub_self, zero_div]
        have : ¬ (χ (a : ZMod ℓ) = 1 ∨ χ (a : ZMod ℓ) = -1) := fun h => h1 (by
          rw [hw]; rcases h with h | h <;> simp [h])
        simp [D, this]

    have hk0 : ∑ a ∈ Finset.range ℓ, (a : ℂ) * χ (a : ZMod ℓ) ^ (2 * 0) = (ℓ : ℂ) * ((ℓ : ℂ) - 1) / 2 := by
      simp only [mul_zero, pow_zero, mul_one]
      have h := congrArg (Nat.cast : ℕ → ℂ) (Finset.sum_range_id_mul_two ℓ)
      have h1 : (1 : ℕ) ≤ ℓ := by omega
      push_cast [Nat.cast_sub h1] at h
      linear_combination h / 2
    have hkpos : ∀ k : ℕ, k + 1 < n →
        ∑ a ∈ Finset.range ℓ, (a : ℂ) * χ (a : ZMod ℓ) ^ (2 * (k + 1)) = 0 := by
      intro k hk'
      set ψ : DirichletCharacter ℂ ℓ := χ ^ (2 * (k + 1)) with hψ
      have hψa : ∀ a : ZMod ℓ, χ a ^ (2 * (k + 1)) = ψ a := fun a => (MulChar.pow_apply' χ (by omega) a).symm
      have hψne : ψ ≠ 1 := by
        intro h
        have := congrArg (fun φ : DirichletCharacter ℂ ℓ => φ (g : ZMod ℓ)) h
        rw [hψ, MulChar.pow_apply_coe, hχg, MulChar.one_apply_coe] at this
        have hdvd := (hζ.pow_eq_one_iff_dvd _).mp this
        have : 2 ^ s ℓ ≤ 2 * (k + 1) := Nat.le_of_dvd (by omega) hdvd
        omega
      have hψev : ψ (-1) = 1 := by
        rw [hψ, MulChar.pow_apply' _ (by omega), hneg, Even.neg_one_pow ⟨k + 1, by ring⟩]
      simp_rw [hψa]
      have hG := hrange (fun x => ((x.val : ℕ) : ℂ) * ψ x)
      rw [hvan ψ hψne hψev] at hG
      rw [← hG]
      refine Finset.sum_congr rfl fun a ha => ?_
      change (a : ℂ) * ψ (a : ZMod ℓ) = (((a : ZMod ℓ).val : ℕ) : ℂ) * ψ (a : ZMod ℓ)
      rw [ZMod.val_cast_of_lt (Finset.mem_range.mp ha)]
    have hmain : (n : ℂ) * ∑ a ∈ Finset.range ℓ, (a : ℂ) * (D a : ℂ) = (ℓ : ℂ) * ((ℓ : ℂ) - 1) / 2 := by
      rw [Finset.mul_sum]
      have h1 : ∀ a ∈ Finset.range ℓ, (n : ℂ) * ((a : ℂ) * (D a : ℂ)) =
          ∑ k ∈ Finset.range n, (a : ℂ) * χ (a : ZMod ℓ) ^ (2 * k) := fun a ha => by
        rw [← Finset.mul_sum, ← hind a ha]; ring
      rw [Finset.sum_congr rfl h1, Finset.sum_comm]
      obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
      rw [hn', Finset.sum_range_succ', hk0]
      rw [Finset.sum_eq_zero (fun k hk => hkpos k (by have := Finset.mem_range.mp hk; omega)), zero_add]

    have hℓ1 : ((ℓ : ℂ) - 1) = 2 * (n : ℂ) * (m ℓ : ℂ) := by
      have : ((ℓ - 1 : ℕ) : ℂ) = ((2 * n * m ℓ : ℕ) : ℂ) := by rw [hn2, hsm]
      push_cast [Nat.cast_sub (show 1 ≤ ℓ by omega)] at this
      exact this
    have hXC : (∑ a ∈ Finset.range ℓ, (a : ℂ) * (D a : ℂ)) = (ℓ : ℂ) * (m ℓ : ℂ) := by
      have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hnpos.ne'
      apply mul_left_cancel₀ hn0
      rw [hmain, hℓ1]
      ring
    have hX : (∑ a ∈ Finset.range ℓ, (a : ℤ) * D a) = (ℓ : ℤ) * (m ℓ : ℤ) := by
      have : ((∑ a ∈ Finset.range ℓ, (a : ℤ) * D a : ℤ) : ℂ) = ((ℓ : ℤ) * (m ℓ : ℤ) : ℤ) := by
        push_cast
        exact hXC
      exact_mod_cast this

    obtain ⟨t, ht⟩ := hdiff
    have hodd : _root_.Odd ((ℓ : ℤ) * (m ℓ : ℤ)) := by
      have h1 : _root_.Odd (ℓ : ℤ) := by exact_mod_cast hp.odd_of_ne_two hℓ
      have h2 : _root_.Odd (m ℓ : ℤ) := by exact_mod_cast hmodd
      exact h1.mul h2
    have : ∑ a ∈ Finset.range ℓ, (a : ℤ) * E a = (ℓ : ℤ) * (m ℓ : ℤ) + 2 * t := by linear_combination ht + hX
    rw [this]
    exact hodd.add_even (even_two_mul t)

#print axioms solution

end S_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum
end P2MW
export P2MW.S_DirichletCharacter_exists_pow_two_pow_eq_one_and_isPrimitive_and_odd_sum (solution)
