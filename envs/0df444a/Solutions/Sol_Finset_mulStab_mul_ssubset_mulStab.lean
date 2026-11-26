-- Prove2me | solution 1 for Finset.mulStab_mul_ssubset_mulStab
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T00:57:26.307227+00:00
-- url     : https://prove2.me/submissions/498a39dc-7cb3-4b79-af99-e0926f8f4119

module
public import Mathlib.Algebra.Ring.Divisibility.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Definitions.Def_Erdos338_Kneser_MulStab
public import Definitions.Def_Erdos338_Kneser_Kneser

set_option autoImplicit true
@[expose] public section
public section
open Function MulAction
open scoped Pointwise
variable {α : Type*} [CommGroup α] [DecidableEq α] {s s' t t' C : Finset α} {a b : α}
open Finset
namespace Finset
theorem _root_.solution (hs₁ : (s ∩ a • C.mulStab).Nonempty)
    (ht₁ : (t ∩ b • C.mulStab).Nonempty) (hab : ¬(a * b) • C.mulStab ⊆ s * t) :
    (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊂ C.mulStab := by
  have hCne : C.Nonempty := by
    contrapose! hab
    simp only [hab, mulStab_empty, smul_finset_empty, empty_subset]
  obtain ⟨x, hx⟩ := hs₁
  obtain ⟨y, hy⟩ := ht₁
  obtain ⟨c, hc, hac⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hx)
  obtain ⟨d, hd, had⟩ := mem_smul_finset.mp (mem_of_mem_inter_right hy)
  have hsubset : (s ∩ a • C.mulStab * (t ∩ b • C.mulStab)).mulStab ⊆ C.mulStab := by
    have hxymem : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
    apply subset_trans (mulStab_subset_div_right hxymem)
    have : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (x * y) • C.mulStab := by
      apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
      rw [smul_mul_smul_comm]
      rw [← hac, ← had, smul_mul_smul_comm, smul_assoc]
      apply smul_finset_subset_smul_finset
      rw [← smul_smul]
      rw [mul_subset_iff]
      intro x hx y hy
      rw [smul_mulStab hd, smul_mulStab hc, mem_mulStab hCne, ← smul_smul,
        (mem_mulStab hCne).mp hy, (mem_mulStab hCne).mp hx]
    apply subset_trans (div_subset_div_right this) _
    simp [singleton_mul, div_eq_inv_mul, smul_smul, mul_assoc]
  have : (a * b) • C.mulStab = (a * c * (b * d)) • C.mulStab := by
    rw [smul_eq_iff_eq_inv_smul, ← smul_assoc, smul_eq_mul, mul_assoc, mul_comm c _, ← mul_assoc, ←
      mul_assoc, ← mul_assoc, mul_assoc _ a b, inv_mul_cancel (a * b), one_mul, ← smul_eq_mul,
      smul_assoc, smul_mulStab hc, smul_mulStab hd]
  have hsub : s ∩ a • C.mulStab * (t ∩ b • C.mulStab) ⊆ (a * b) • C.mulStab := by
    apply subset_trans (mul_subset_mul inter_subset_right inter_subset_right)
    simp only [smul_mul_smul_comm, mulStab_mul_mulStab, subset_refl]
  have hxy : x * y ∈ s ∩ a • C.mulStab * (t ∩ b • C.mulStab) := mul_mem_mul hx hy
  rw [this] at hsub
  rw [this] at hab
  obtain ⟨z, hz, hzst⟩ := not_subset.1 hab
  obtain ⟨w, hw, hwz⟩ := mem_smul_finset.mp hz
  refine (Finset.ssubset_iff_of_subset hsubset).mpr ⟨w, hw, ?_⟩
  rw [mem_mulStab' ⟨x * y, hxy⟩]
  push Not
  refine ⟨a * c * (b * d), by simp_all, ?_⟩
  rw [smul_eq_mul, mul_comm w, ← smul_eq_mul (b := w), hwz]
  exact notMem_mono (mul_subset_mul inter_subset_left inter_subset_left) hzst
end Finset
