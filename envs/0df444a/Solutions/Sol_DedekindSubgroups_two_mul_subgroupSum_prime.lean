-- Prove2me | solution 1 for DedekindSubgroups.two_mul_subgroupSum_prime
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:15:42.508563+00:00
-- url     : https://prove2.me/submissions/961bbdb5-37f9-4b72-82c6-181ff51baa09

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime
public import Theorems.Thm_DedekindSubgroups_E_cast
public import Theorems.Thm_DedekindSubgroups_twelve_ne_zero
public import Theorems.Thm_DedekindSubgroups_E_modp
public import Theorems.Thm_DedekindSubgroups_sum_inv_eq_sum
public import Theorems.Thm_DedekindSubgroups_sum_subgroup_eq_zero
public import Theorems.Thm_DedekindSubgroups_card_filter_mem
public import Theorems.Thm_DedekindSubgroups_dedekindSum_residue
public import Theorems.Thm_DedekindSubgroups_twelve_mul_subgroupSum_modEq
public import Theorems.Thm_DedekindSubgroups_val_mul_val_inv


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution {p : ℕ} [hp : Fact p.Prime] (hp3 : 3 < p)
    (H : Subgroup (ZMod p)ˣ) (hodd : Odd (Nat.card H)) (hn : 1 < Nat.card H) :
    ∃ y : ℤ, (y : ℚ) = 2 * subgroupSum H ∧
      y ≡ (Nat.card H : ℤ) * (((p : ℤ) - 1) / 2) [ZMOD 8] := by
  classical
  have hp1 : 1 < p := hp.out.one_lt
  have hp0 : 0 < p := hp.out.pos
  have hH : H ≠ ⊥ := fun h => by rw [(Subgroup.eq_bot_iff_card H).mp h] at hn; omega
  set s := univ.filter (· ∈ H) with hs
  have hcard : s.card = Nat.card H := card_filter_mem H
  -- `p` is odd
  obtain ⟨m, hm⟩ : Odd p := hp.out.odd_of_ne_two (by omega)
  have hpm : (p : ℤ) = 2 * m + 1 := by exact_mod_cast hm
  have hhalf : ((p : ℤ) - 1) / 2 = m := by omega
  -- the integers `e_u`
  have he : ∀ u : (ZMod p)ˣ, ∃ e : ℤ, E (u : ZMod p).val p = p * e ∧
      (((12 * e : ℤ)) : ZMod p) = (((u : ZMod p).val : ℕ) : ZMod p)
        + ((((u⁻¹ : (ZMod p)ˣ) : ZMod p).val : ℕ) : ZMod p) :=
    fun u => E_modp hp3 (val_mul_val_inv hp1 u)
  choose e heE hemod using he
  -- `p ∣ ∑ e_u`
  have h12 : (12 : ZMod p) ≠ 0 := twelve_ne_zero hp3
  have hsum0 : ((∑ u ∈ s, e u : ℤ) : ZMod p) = 0 := by
    have h1 : (12 : ZMod p) * ((∑ u ∈ s, e u : ℤ) : ZMod p) = 0 := by
      push_cast
      rw [mul_sum]
      have : ∀ u ∈ s, (12 : ZMod p) * (e u : ZMod p)
          = ((u : (ZMod p)ˣ) : ZMod p) + ((u⁻¹ : (ZMod p)ˣ) : ZMod p) := by
        intro u _
        have := hemod u
        push_cast at this
        rw [this, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val, Units.val_inv_eq_inv_val]
      rw [sum_congr rfl this, sum_add_distrib, sum_inv_eq_sum, sum_subgroup_eq_zero H hH, add_zero]
    exact (mul_eq_zero.mp h1).resolve_left h12
  obtain ⟨f, hf⟩ := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mp hsum0
  -- `2 S(H,p) = 2 f - n m`
  set n : ℕ := Nat.card H with hn_def
  have hS : subgroupSum H = (f : ℚ) - n * (2 * m) / 4 := by
    have hpq : (p : ℚ) ≠ 0 := by exact_mod_cast hp0.ne'
    have hterm : ∀ u ∈ s, dedekindSum (u : ZMod p).val p = (e u : ℚ) / p - ((p : ℚ) - 1) / 4 := by
      intro u _
      rw [dedekindSum_residue hp0 (val_mul_val_inv hp1 u), ← E_cast, heE u]
      push_cast
      field_simp
    unfold subgroupSum
    rw [← hs, sum_congr rfl hterm, sum_sub_distrib, ← sum_div, sum_const, hcard, nsmul_eq_mul]
    have hf' : (∑ u ∈ s, (e u : ℚ)) = p * f := by exact_mod_cast hf
    have hpm' : (p : ℚ) = 2 * m + 1 := by exact_mod_cast hpm
    rw [hf']
    field_simp
    rw [hpm']
    ring
  refine ⟨2 * f - n * m, ?_, ?_⟩
  · rw [hS]; push_cast; ring
  · -- the congruence, from Theorem 1.1
    rw [hhalf]
    obtain ⟨N, hN, hNmod⟩ := twelve_mul_subgroupSum_modEq hp1 H hodd
    have h6 : N = 6 * p * (2 * f - n * m) := by
      have : (N : ℚ) = 6 * p * (2 * f - n * m) := by
        rw [hN, hS]
        have hpm' : (p : ℚ) = 2 * m + 1 := by exact_mod_cast hpm
        rw [hpm']; ring
      exact_mod_cast this
    rw [h6] at hNmod
    obtain ⟨t, ht⟩ := Int.modEq_iff_dvd.mp hNmod
    rw [hpm] at ht
    -- halve
    have ht2 : (n : ℤ) * m * (2 * m - 1) - 3 * (2 * m + 1) * (2 * f - n * m) = 8 * t := by
      refine mul_left_cancel₀ (two_ne_zero : (2 : ℤ) ≠ 0) ?_
      linear_combination ht
    obtain ⟨a, ha⟩ := Int.even_mul_succ_self (m : ℤ)
    refine (Int.modEq_iff_dvd.mpr ⟨-(3 * t * (2 * m + 1) - n * (3 * a * (m - 1) + m)
      + 9 * a * (2 * f - n * m) + (2 * f - n * m)), ?_⟩).symm
    linear_combination (-3) * (2 * (m : ℤ) + 1) * ht2
      + (12 * (n : ℤ) * (m - 1) - 36 * (2 * f - n * m)) * ha
end DedekindSubgroups
