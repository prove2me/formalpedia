-- Prove2me | solution 1 for GallaiEdmonds.cc_subset_of_closed
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T01:57:16.419583+00:00
-- url     : https://prove2.me/submissions/bac1c59e-719d-4fa5-8073-dd07167c6c4d

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEComponents

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*}
variable {G : SimpleGraph V} {W W' S : Set V} {x y z : V}
namespace GallaiEdmonds
theorem _root_.solution (hxS : x ∈ S) (hS : ∀ y ∈ S, ∀ z ∈ W, G.Adj y z → z ∈ S) :
    cc G W x ⊆ S := by
  rintro y ⟨hx, hy, ⟨p⟩⟩
  suffices h : ∀ (a b : W) (_ : (G.induce W).Walk a b), a.1 ∈ S → b.1 ∈ S from h _ _ p hxS
  intro a b p
  induction p with
  | nil => exact id
  | cons h p ih => exact fun ha => ih (hS _ ha _ (Subtype.prop _) h)
end GallaiEdmonds
