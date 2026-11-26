-- Prove2me | solution 1 for GallaiEdmonds.oddPart_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:19.072308+00:00
-- url     : https://prove2.me/submissions/c4ad78c2-013b-44a5-be6a-175a1b1c9979

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_cc_eq_of_mem
public import Theorems.Thm_GallaiEdmonds_mem_cc_of_adj
public import Theorems.Thm_GallaiEdmonds_mem_cc_self


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution (U : Set V) : Closed G Uᶜ (oddPart G U) := by
  rintro y ⟨hyU, hodd⟩ z hz hadj
  have hzy : z ∈ cc G Uᶜ y := mem_cc_of_adj (mem_cc_self hyU) hz hadj
  exact ⟨hz, by rw [cc_eq_of_mem hzy]; exact hodd⟩
end GallaiEdmonds
