-- Prove2me | solution 1 for DedekindSubgroups.subgroupSum_eq_of_mem_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:11:05.156814+00:00
-- url     : https://prove2.me/submissions/2aede816-cc64-4c5f-abb2-0367c4507376

module
public import Definitions.Def_DedekindSubgroups_Prime
public import Definitions.Def_DedekindSubgroups_Optimality

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution {k : ℕ} [NeZero k] (H : Subgroup (ZMod k)ˣ)
    (t : Finset (ZMod k)ˣ) (ht : ∀ x, x ∈ H ↔ x ∈ t) :
    subgroupSum H = ∑ u ∈ t, dedekindSum (u : ZMod k).val k := by
  classical
  unfold subgroupSum
  congr 1
  ext x
  simp [ht]
end DedekindSubgroups
