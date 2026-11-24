-- Prove2me | solution 1 for FFactor.F3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:04:15.902426+00:00
-- url     : https://prove2.me/submissions/f2c3682e-18c7-425d-b955-7fa825246c73

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_outer_notMem_of_outer_notMem
public import Theorems.Thm_FFactor_mem_Sset

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution (hmin : ∀ x ∈ U, ¬ TwoComp (gadget G f) U x) {v : V} (hvT : v ∉ Tset G f U)
    (hvS : v ∉ Sset G f U) {d : G.Dart} (hd : d.fst = v) : (.inl d : GV G f) ∉ U := by
  have : ¬ ∀ d : G.Dart, d.fst = v → (.inl d : GV G f) ∈ U := fun h =>
    hvS (mem_Sset.mpr ⟨hvT, h⟩)
  push Not at this
  obtain ⟨z, hz, hzU⟩ := this
  exact outer_notMem_of_outer_notMem hmin (F1 hmin hvT) hz hzU hd
end FFactor
