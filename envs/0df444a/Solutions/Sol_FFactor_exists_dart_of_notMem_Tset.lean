-- Prove2me | solution 1 for FFactor.exists_dart_of_notMem_Tset
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:03:01.451567+00:00
-- url     : https://prove2.me/submissions/8638c3e1-8189-4712-b17b-5839401e95e5

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_exists_inner_of_notMem_Tset

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution {v : V} (hv : v ∉ Tset G f U) :
    ∃ d : G.Dart, d.fst = v := by
  obtain ⟨i, -⟩ := exists_inner_of_notMem_Tset hv
  have : 0 < G.degree v := by have := i.2; omega
  obtain ⟨u, hu⟩ := G.degree_pos_iff_exists_adj v |>.mp this
  exact ⟨⟨(v, u), hu⟩, rfl⟩
end FFactor
