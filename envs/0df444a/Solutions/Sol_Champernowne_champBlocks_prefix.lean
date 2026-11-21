-- Prove2me | solution 1 for Champernowne.champBlocks_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:36:44.852744+00:00
-- url     : https://prove2.me/submissions/13d493cc-d2df-4c41-8559-1200d1ab5367

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Definitions.Def_LeanPool_Champernowne_Prefix

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
namespace Champernowne
theorem _root_.solution {b N M : ℕ} (h : N ≤ M) :
    champBlocks b N <+: champBlocks b M := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  simp only [champBlocks, List.range_add, List.map_append, List.flatten_append]
  exact List.prefix_append _ _
end Champernowne
