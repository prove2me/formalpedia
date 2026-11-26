-- Prove2me | solution 1 for BandParity.half_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T22:58:27.688054+00:00
-- url     : https://prove2.me/submissions/28fa4591-6753-43c1-b38b-c772dd0e086f

module
public import Definitions.Def_BandParity_Basic
public import Definitions.Def_BandParity_FixedBase
public import Theorems.Thm_BandParity_fixed_base_collapse
public import Theorems.Thm_BandParity_val_neg_of_ne_zero
public import Theorems.Thm_BandParity_gi_im
public import Theorems.Thm_BandParity_gi_re
attribute [local simp] BandParity.gi_im
attribute [local simp] BandParity.gi_re



set_option autoImplicit true
@[expose] public section
public section
open BandParity
open Finset
variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R]
namespace BandParity
theorem _root_.solution (hp2 : p ≠ 2) (χ : MulChar (ZMod p) R) (hodd : χ (-1) = -1) :
    (p : R) * χ 2 * ∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), χ n =
      (1 - 2 * χ 2) * T χ := by
  have h20 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 this)
  have hpodd : p % 2 = 1 := (hp.out.eq_two_or_odd).resolve_left hp2
  have h2val : (2 : ZMod p).val = 2 := by
    have : 2 < p := lt_of_le_of_ne hp.out.two_le (Ne.symm hp2)
    rw [show (2 : ZMod p) = ((2 : ℕ) : ZMod p) by norm_cast, ZMod.val_natCast,
      Nat.mod_eq_of_lt this]
  have key := fixed_base_collapse χ h20
  rw [h2val] at key
  -- `floorSum χ 2 = ∑_{2n ≥ p} χ n = - ∑_{2n < p} χ n`
  have hfl : floorSum χ 2 = -∑ n ∈ univ.filter (fun n : ZMod p => 2 * n.val < p), χ n := by
    unfold floorSum
    rw [h2val]
    have h1 : ∀ n : ZMod p, χ n * ((2 * n.val / p : ℕ) : R) =
        if p ≤ 2 * n.val then χ n else 0 := by
      intro n
      have hn := ZMod.val_lt n
      by_cases h : p ≤ 2 * n.val
      · rw [show 2 * n.val / p = 1 from Nat.div_eq_of_lt_le (by omega) (by omega)]
        simp [h]
      · rw [Nat.div_eq_of_lt (by omega)]; simp [h]
    simp_rw [h1]
    rw [Finset.sum_filter, ← Finset.sum_neg_distrib]
    refine Fintype.sum_equiv (Equiv.neg (ZMod p)) _ _ fun n => ?_
    simp only [Equiv.neg_apply]
    by_cases hn0 : n = 0
    · subst hn0; simp [MulChar.map_zero]
    · rw [val_neg_of_ne_zero hn0]
      have hn := ZMod.val_lt n
      have hχn : χ (-n) = -χ n := by
        rw [neg_eq_neg_one_mul, map_mul, hodd, neg_one_mul]
      by_cases h : p ≤ 2 * n.val
      · have h' : 2 * (p - n.val) < p := by omega
        simp [h, h', hχn]
      · have h' : ¬ 2 * (p - n.val) < p := by omega
        simp [h, h']
  rw [hfl] at key
  linear_combination -key
end BandParity
