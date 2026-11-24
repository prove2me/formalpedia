-- Prove2me | solution 1 for FFactor.F5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:59:08.258283+00:00
-- url     : https://prove2.me/submissions/fea36561-bd0a-48d3-8425-5eaf556e26f0

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
theorem _root_.solution {v : V} (hv : v ∈ Tset G f U) (i : Fin (G.degree v - f v)) :
    (.inr ⟨v, i⟩ : GV G f) ∈ U :=
  mem_Tset.mp hv i
end FFactor
