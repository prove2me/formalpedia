-- Prove2me | solution 1 for GallaiEdmonds.exists_minBarrier
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:07:55.605861+00:00
-- url     : https://prove2.me/submissions/ae3adf08-1ae4-46c7-828b-47518db060cb

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEMatching
public import Definitions.Def_GallaiEdmondsLib_GEBarrier
public import Theorems.Thm_GallaiEdmonds_tb_eq


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} {G : SimpleGraph V}
namespace GallaiEdmonds
theorem _root_.solution [Finite V] (G : SimpleGraph V) : ∃ U, IsMinBarrier G U := by
  classical
  obtain ⟨M, U, hM, -, h⟩ := tb_eq G
  have hex : ∃ n, ∃ U, IsBarrier G U ∧ (oddPart G U).ncard = n := ⟨_, U, ⟨M, hM, h⟩, rfl⟩
  obtain ⟨U0, hU0, hn⟩ := Nat.find_spec hex
  refine ⟨U0, hU0, fun U' hU' => ?_⟩
  rw [hn]
  exact Nat.find_min' hex ⟨U', hU', rfl⟩
end GallaiEdmonds
