-- Prove2me | solution 1 for FFactor.oddCnt_le_of_factor
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:04:12.615809+00:00
-- url     : https://prove2.me/submissions/ae9dc6bb-c9f0-4fb6-a3ef-6b3071d772a4

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorNec
public import Theorems.Thm_FFactor_oddCnt_le_card_witness
public import Theorems.Thm_FFactor_card_witness_le

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V]
open Classical
namespace FFactor
theorem _root_.solution (G H : SimpleGraph V) (hHG : H ≤ G) (f : V → ℕ)
    (hdeg : ∀ v, #{u | H.Adj v u} = f v) (S T : Finset V) (hST : Disjoint S T) :
    (oddCnt G f S T : ℤ) ≤
      ∑ v ∈ S, (f v : ℤ) - ∑ v ∈ T, (f v : ℤ) + ∑ v ∈ T, (#{u | G.Adj v u ∧ u ∉ S} : ℤ) :=
  (Nat.cast_le.mpr (oddCnt_le_card_witness G H hHG f hdeg S T)).trans
    (card_witness_le G H hHG f hdeg S T hST)
end FFactor
