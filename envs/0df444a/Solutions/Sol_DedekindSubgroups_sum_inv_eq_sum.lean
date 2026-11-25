-- Prove2me | solution 1 for DedekindSubgroups.sum_inv_eq_sum
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:10:23.376977+00:00
-- url     : https://prove2.me/submissions/e645e4d7-cd6a-4cd4-b87c-a2bb8655bd7f

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
theorem _root_.solution (H : Subgroup (ZMod p)ˣ) [DecidablePred (· ∈ H)] :
    ∑ u ∈ univ.filter (· ∈ H), ((u⁻¹ : (ZMod p)ˣ) : ZMod p)
      = ∑ u ∈ univ.filter (· ∈ H), ((u : (ZMod p)ˣ) : ZMod p) := by
  refine sum_nbij' (fun u => u⁻¹) (fun u => u⁻¹) ?_ ?_ ?_ ?_ ?_
  · intro u hu; exact mem_filter.mpr ⟨mem_univ _, H.inv_mem (mem_filter.mp hu).2⟩
  · intro u hu; exact mem_filter.mpr ⟨mem_univ _, H.inv_mem (mem_filter.mp hu).2⟩
  · intro u _; exact inv_inv u
  · intro u _; exact inv_inv u
  · intro u _; rfl
end DedekindSubgroups
