-- Prove2me | solution 1 for FFactor.exists_inner_of_notMem_Tset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:56:46.784007+00:00
-- url     : https://prove2.me/submissions/c7801f4d-ea49-4bee-9c43-05298df8667d

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution {v : V} (hv : v ∉ Tset G f U) :
    ∃ _ : Fin (G.degree v - f v), True := by
  by_contra h
  push Not at h
  exact hv (mem_Tset.mpr (fun i => (h i).elim))
end FFactor
