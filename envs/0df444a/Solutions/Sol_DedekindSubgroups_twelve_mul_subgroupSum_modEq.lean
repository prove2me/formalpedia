-- Prove2me | solution 1 for DedekindSubgroups.twelve_mul_subgroupSum_modEq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:11:46.183852+00:00
-- url     : https://prove2.me/submissions/11f7d08f-85ba-4bad-8c66-61ffc68e3340

module
public import Definitions.Def_DedekindSubgroups_Parity
public import Definitions.Def_DedekindSubgroups_Main
public import Theorems.Thm_DedekindSubgroups_val_mul_val_inv
public import Theorems.Thm_DedekindSubgroups_inv_one_eq_zero
public import Theorems.Thm_DedekindSubgroups_sq_root_of_odd
public import Theorems.Thm_DedekindSubgroups_eq_one_of_inv_eq
public import Theorems.Thm_DedekindSubgroups_even_inv_sq
public import Theorems.Thm_DedekindSubgroups_inv_symm
public import Theorems.Thm_DedekindSubgroups_meyer


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {k : ℕ} [NeZero k]
namespace DedekindSubgroups
theorem _root_.solution (hk : 1 < k) (H : Subgroup (ZMod k)ˣ)
    (hodd : Odd (Nat.card H)) :
    ∃ N : ℤ, (N : ℚ) = 12 * k * subgroupSum H ∧
      N ≡ (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) [ZMOD 16] := by
  classical
  have hk0 : 0 < k := lt_trans Nat.zero_lt_one hk
  set s : Finset (ZMod k)ˣ := univ.filter (· ∈ H) with hs
  have hcard : s.card = Nat.card H := by
    rw [hs, Nat.card_eq_fintype_card]
    convert (Fintype.card_subtype (· ∈ H)).symm
  -- the integer inversion counts
  let I : (ZMod k)ˣ → ℕ := fun u => inv (u : ZMod k).val k
  have hmeyer : ∀ u : (ZMod k)ˣ,
      12 * (k : ℚ) * dedekindSum (u : ZMod k).val k = ((k : ℚ) - 1) * ((k : ℚ) - 2) - 4 * I u :=
    fun u => meyer hk0 (val_mul_val_inv hk u)
  refine ⟨(s.card : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) - 4 * ∑ u ∈ s, (I u : ℤ), ?_, ?_⟩
  · -- the integer equals 12 k S(H,k)
    unfold subgroupSum
    rw [← hs]
    have hR : 12 * (k : ℚ) * ∑ u ∈ s, dedekindSum (u : ZMod k).val k
        = ∑ u ∈ s, (((k : ℚ) - 1) * ((k : ℚ) - 2) - 4 * I u) := by
      rw [mul_sum]; exact sum_congr rfl (fun u _ => hmeyer u)
    rw [hR, sum_sub_distrib, sum_const, ← mul_sum]
    push_cast
    ring
  · -- every inversion count is even, and inverse elements have equal counts
    rw [hcard]
    have heven : ∀ u ∈ s, Even (I u) := by
      intro u hu
      have huH : u ∈ H := (mem_filter.mp hu).2
      -- u is the square of w = u^((n+1)/2), computed inside H
      set w : H := (⟨u, huH⟩ : H) ^ ((Nat.card H + 1) / 2)
      have hw : (w : (ZMod k)ˣ) * (w : (ZMod k)ˣ) = u := by
        have := sq_root_of_odd hodd (⟨u, huH⟩ : H)
        exact congrArg Subtype.val this
      have hval : (u : ZMod k).val = ((w : (ZMod k)ˣ) : ZMod k).val * ((w : (ZMod k)ˣ) : ZMod k).val % k := by
        rw [← ZMod.val_mul, ← Units.val_mul, hw]
      show Even (inv (u : ZMod k).val k)
      rw [hval]
      exact even_inv_sq hk0 (val_mul_val_inv hk (w : (ZMod k)ˣ))
    have hsym : ∀ u : (ZMod k)ˣ, I u⁻¹ = I u := fun u => inv_symm hk0 (val_mul_val_inv hk u)
    -- write each count as twice a natural number and pair u with u⁻¹ in ZMod 2
    let J : (ZMod k)ˣ → ℕ := fun u => I u / 2
    have hIJ : ∀ u ∈ s, (I u : ℤ) = 2 * J u := by
      intro u hu
      obtain ⟨m, hm⟩ := heven u hu
      simp only [J, hm]; omega
    have hJsym : ∀ u, J u⁻¹ = J u := fun u => by simp only [J, hsym u]
    have hpair : ∑ u ∈ s, ((J u : ℕ) : ZMod 2) = 0 := by
      refine Finset.sum_involution (fun u _ => u⁻¹) ?_ ?_ ?_ ?_
      · intro u _
        rw [hJsym u, ← two_mul]
        exact (by decide : (2 : ZMod 2) = 0) ▸ zero_mul _
      · intro u hu hne heq
        apply hne
        have hu1 : u = 1 := by
          have hH : (⟨u, (mem_filter.mp hu).2⟩ : H) = 1 :=
            eq_one_of_inv_eq hodd (Subtype.ext heq)
          exact congrArg Subtype.val hH
        subst hu1
        have : Fact (1 < k) := ⟨hk⟩
        simp only [J, I, Units.val_one, ZMod.val_one, inv_one_eq_zero, Nat.zero_div, Nat.cast_zero]
      · intro u hu
        exact mem_filter.mpr ⟨mem_univ _, H.inv_mem (mem_filter.mp hu).2⟩
      · intro u _; exact inv_inv u
    have h2 : (2 : ℤ) ∣ ∑ u ∈ s, (J u : ℤ) := by
      have : ((∑ u ∈ s, J u : ℕ) : ZMod 2) = 0 := by push_cast; exact hpair
      have h2n : 2 ∣ ∑ u ∈ s, J u := (ZMod.natCast_eq_zero_iff _ 2).mp this
      exact_mod_cast h2n
    have hsumI : ∑ u ∈ s, (I u : ℤ) = 2 * ∑ u ∈ s, (J u : ℤ) := by
      rw [mul_sum]; exact sum_congr rfl hIJ
    obtain ⟨c, hc⟩ := h2
    rw [hsumI, hc]
    refine Int.ModEq.symm (Int.modEq_iff_dvd.mpr ⟨-c, by ring⟩)
end DedekindSubgroups
