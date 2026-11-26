-- Prove2me | solution 1 for GallaiEdmonds.mem_setC_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:14:32.487524+00:00
-- url     : https://prove2.me/submissions/0d49ffae-3dcc-49b7-b355-5e5fc65da4b6

module
public import Mathlib
public import Definitions.Def_BergeLib_Berge
public import Definitions.Def_GallaiEdmondsLib_GEConstruct
public import Definitions.Def_GallaiEdmondsLib_GallaiEdmonds
public import Theorems.Thm_GallaiEdmonds_setD_eq
public import Theorems.Thm_GallaiEdmonds_setA_eq

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open GallaiEdmonds
variable {V : Type*} (G : SimpleGraph V)
namespace GallaiEdmonds
theorem _root_.solution [Finite V] {U : Set V} (hU : IsMinBarrier G U) (w : V) :
    w ∈ setC G ↔ w ∉ U ∧ Even (cc G Uᶜ w).ncard := by
  simp only [setC, setD_eq G hU, setA_eq G hU, Set.mem_ofPred_eq, oddPart,
    ← Nat.not_odd_iff_even]
  tauto
end GallaiEdmonds
