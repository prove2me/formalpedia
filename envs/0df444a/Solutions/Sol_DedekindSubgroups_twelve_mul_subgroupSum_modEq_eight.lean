-- Prove2me | solution 1 for DedekindSubgroups.twelve_mul_subgroupSum_modEq_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:13:28.778166+00:00
-- url     : https://prove2.me/submissions/b0754996-4126-48f2-8c39-f5d6cba49c2b

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_General
public import Theorems.Thm_DedekindSubgroups_inv_symm
public import Theorems.Thm_DedekindSubgroups_meyer
public import Theorems.Thm_DedekindSubgroups_val_mul_val_inv


set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {k : ℕ} [NeZero k]
open Classical
namespace DedekindSubgroups
theorem _root_.solution (hk : 1 < k) (H : Subgroup (ZMod k)ˣ) :
    ∃ N : ℤ, (N : ℚ) = 12 * k * subgroupSum H ∧
      N ≡ (Nat.card H : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2))
        - 4 * ∑ u ∈ (univ.filter (· ∈ H)).filter (fun u => u * u = 1),
            (inv (u : ZMod k).val k : ℤ) [ZMOD 8] := by
  have hk0 : 0 < k := lt_trans Nat.zero_lt_one hk
  set s : Finset (ZMod k)ˣ := univ.filter (· ∈ H) with hs
  have hcard : s.card = Nat.card H := by
    rw [hs, Nat.card_eq_fintype_card]
    convert (Fintype.card_subtype (· ∈ H)).symm
  let I : (ZMod k)ˣ → ℕ := fun u => inv (u : ZMod k).val k
  have hmeyer : ∀ u : (ZMod k)ˣ,
      12 * (k : ℚ) * dedekindSum (u : ZMod k).val k = ((k : ℚ) - 1) * ((k : ℚ) - 2) - 4 * I u :=
    fun u => meyer hk0 (val_mul_val_inv hk u)
  refine ⟨(s.card : ℤ) * (((k : ℤ) - 1) * ((k : ℤ) - 2)) - 4 * ∑ u ∈ s, (I u : ℤ), ?_, ?_⟩
  · unfold subgroupSum
    rw [← hs]
    have hR : 12 * (k : ℚ) * ∑ u ∈ s, dedekindSum (u : ZMod k).val k
        = ∑ u ∈ s, (((k : ℚ) - 1) * ((k : ℚ) - 2) - 4 * I u) := by
      rw [mul_sum]; exact sum_congr rfl (fun u _ => hmeyer u)
    rw [hR, sum_sub_distrib, sum_const, ← mul_sum]
    push_cast
    ring
  · rw [hcard]
    have hsym : ∀ u : (ZMod k)ˣ, I u⁻¹ = I u := fun u => inv_symm hk0 (val_mul_val_inv hk u)
    -- the elements with `u² ≠ 1` pair off with their inverses
    have hpair : ∑ u ∈ s.filter (fun u => ¬ u * u = 1), ((I u : ℕ) : ZMod 2) = 0 := by
      refine Finset.sum_involution (fun u _ => u⁻¹) ?_ ?_ ?_ ?_
      · intro u _
        rw [hsym u, ← two_mul]
        exact (by decide : (2 : ZMod 2) = 0) ▸ zero_mul _
      · intro u hu _ heq
        have h2 : ¬ u * u = 1 := (mem_filter.mp hu).2
        apply h2
        calc u * u = u⁻¹ * u := by rw [heq]
          _ = 1 := inv_mul_cancel u
      · intro u hu
        obtain ⟨hu1, hu2⟩ := mem_filter.mp hu
        refine mem_filter.mpr ⟨mem_filter.mpr ⟨mem_univ _, H.inv_mem (mem_filter.mp hu1).2⟩, ?_⟩
        intro h
        apply hu2
        rw [← mul_inv_rev] at h
        exact inv_eq_one.mp h
      · intro u _; exact inv_inv u
    have h2 : (2 : ℤ) ∣ ∑ u ∈ s.filter (fun u => ¬ u * u = 1), (I u : ℤ) := by
      have : ((∑ u ∈ s.filter (fun u => ¬ u * u = 1), I u : ℕ) : ZMod 2) = 0 := by
        push_cast; exact hpair
      have h2n : 2 ∣ ∑ u ∈ s.filter (fun u => ¬ u * u = 1), I u :=
        (ZMod.natCast_eq_zero_iff _ 2).mp this
      exact_mod_cast h2n
    obtain ⟨c, hc⟩ := h2
    have hsplit := sum_filter_add_sum_filter_not s (fun u => u * u = 1) (fun u => (I u : ℤ))
    refine Int.modEq_iff_dvd.mpr ⟨c, ?_⟩
    rw [← hsplit, hc]
    ring
end DedekindSubgroups
