-- Prove2me | solution 1 for GallaiEdmonds.compSet_mem_oddComps
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:33.053946+00:00
-- url     : https://prove2.me/submissions/785be921-4fd1-4589-97af-b0e5b67f2856

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_setD_eq
public import Theorems.Thm_GallaiEdmonds_compSet_mk
public import Theorems.Thm_GallaiEdmonds_cc_mem_comps


set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U)
    (c : (G.induce (setD G)).ConnectedComponent) : compSet G c ∈ oddComps G Uᶜ := by
  induction c using ConnectedComponent.ind with
  | h a =>
    obtain ⟨x, hx⟩ := a
    have hxO : x ∈ oddPart G U := setD_eq G hU ▸ hx
    rw [compSet_mk G hU]
    exact ⟨cc_mem_comps hxO.1, hxO.2⟩
end GallaiEdmonds
