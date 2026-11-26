-- Prove2me | solution 1 for BrooksTheorem.Aux.mem_nb
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:25:55.611568+00:00
-- url     : https://prove2.me/submissions/52c2c4d4-09ec-47ea-9ddb-f679c5269e0b

module
public import Mathlib
public import Definitions.Def_BrooksLib_Greedy

set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph Finset
open BrooksTheorem
open BrooksTheorem.Aux
variable {V : Type*}
variable [Fintype V]
namespace BrooksTheorem.Aux
theorem _root_.solution {H : SimpleGraph V} {v u : V} : u ∈ nb H v ↔ H.Adj v u := by
  simp [nb]
end BrooksTheorem.Aux
