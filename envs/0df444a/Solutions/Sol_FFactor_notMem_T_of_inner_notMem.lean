-- Prove2me | solution 1 for FFactor.notMem_T_of_inner_notMem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:01:11.352289+00:00
-- url     : https://prove2.me/submissions/367d4133-e5aa-4428-a72a-852f02c10089

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorComp
public import Definitions.Def_FFactorLib_FFactorGadget
public import Definitions.Def_FFactorLib_FFactorSuff
public import Theorems.Thm_FFactor_F5

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] {G : SimpleGraph V} {f : V → ℕ}
variable [DecidableEq V] {U : Set (GV G f)}
omit [DecidableEq V]
namespace FFactor
theorem _root_.solution {v : V} {i : Fin (G.degree v - f v)}
    (h : (.inr ⟨v, i⟩ : GV G f) ∉ U) : v ∉ Tset G f U := fun hv => h (F5 hv i)
end FFactor
