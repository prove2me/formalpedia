-- Prove2me | solution 1 for DedekindSubgroups.sum_subgroup_eq_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:11:25.704309+00:00
-- url     : https://prove2.me/submissions/28ce0d14-6985-406a-905f-5e5762586ab3

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
variable {p : ℕ} [Fact p.Prime]
namespace DedekindSubgroups
theorem _root_.solution (H : Subgroup (ZMod p)ˣ) [DecidablePred (· ∈ H)] (hH : H ≠ ⊥) :
    ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) = 0 := by
  obtain ⟨⟨g, hgH⟩, hg1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hH
  have hg1' : (g : ZMod p) ≠ 1 := by
    intro h; apply hg1; ext; simpa using h
  have hmul : ∑ u ∈ univ.filter (· ∈ H), (g : ZMod p) * ((u : (ZMod p)ˣ) : ZMod p)
      = ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) := by
    refine sum_nbij' (fun u => g * u) (fun u => g⁻¹ * u) ?_ ?_ ?_ ?_ ?_
    · intro u hu; exact mem_filter.mpr ⟨mem_univ _, H.mul_mem hgH (mem_filter.mp hu).2⟩
    · intro u hu
      exact mem_filter.mpr ⟨mem_univ _, H.mul_mem (H.inv_mem hgH) (mem_filter.mp hu).2⟩
    · intro u _; simp
    · intro u _; simp
    · intro u _; simp
  rw [← mul_sum] at hmul
  have : ((g : ZMod p) - 1) * ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) = 0 := by
    rw [sub_mul, hmul, one_mul, sub_self]
  exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr hg1')
end DedekindSubgroups
