-- Prove2me | solution 1 for DedekindSubgroups.card_filter_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-25T21:13:05.352286+00:00
-- url     : https://prove2.me/submissions/2c7391e9-06f9-4552-bbcf-009e2ca75195

module
public import Definitions.Def_DedekindSubgroups_Main
public import Definitions.Def_DedekindSubgroups_Prime

set_option autoImplicit true
@[expose] public section
public section
open Finset
open DedekindSubgroups
namespace DedekindSubgroups
theorem _root_.solution {k : ℕ} [NeZero k] (H : Subgroup (ZMod k)ˣ) [DecidablePred (· ∈ H)] :
    (univ.filter (· ∈ H)).card = Nat.card H := by
  rw [Nat.card_eq_fintype_card]
  convert (Fintype.card_subtype (· ∈ H)).symm
end DedekindSubgroups
