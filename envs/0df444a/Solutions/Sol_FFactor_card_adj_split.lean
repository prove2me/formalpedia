-- Prove2me | solution 1 for FFactor.card_adj_split
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T06:05:02.226668+00:00
-- url     : https://prove2.me/submissions/5e85f7bd-9f5a-4342-8085-3d0a8dd5ec0b

module
public import Mathlib
public import Definitions.Def_FFactorLib_FFactorDefs
public import Definitions.Def_FFactorLib_FFactorSuff
public import Definitions.Def_FFactorLib_FFactorCount
public import Theorems.Thm_FFactor_card_adj_eq_degree

set_option autoImplicit true
@[expose] public section
public section
open Finset SimpleGraph Classical
open FFactor
variable {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {f : V → ℕ}
  {U : Set (GV G f)}
namespace FFactor
theorem _root_.solution (t : V) (S : Finset V) :
    #{u | G.Adj t u ∧ u ∈ S} + #{u | G.Adj t u ∧ u ∉ S} = G.degree t := by
  rw [← card_adj_eq_degree, ← card_filter_add_card_filter_not (s := {u | G.Adj t u})
    (fun u => u ∈ S), filter_filter, filter_filter]
end FFactor
