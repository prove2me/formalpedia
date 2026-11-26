-- Prove2me | solution 1 for GallaiEdmonds.oddPart_subset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:05:32.319937+00:00
-- url     : https://prove2.me/submissions/1bb675e7-959d-47ec-8263-fcc1349dfb7d

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution (U : Set V) : oddPart G U ⊆ Uᶜ := fun _ hy => hy.1
end GallaiEdmonds
