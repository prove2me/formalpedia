-- Prove2me | solution 1 for GJKKL.Main.empty_mem_matchingsOfSize
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T13:22:58.141444+00:00
-- url     : https://prove2.me/submissions/8aa78cc6-d5a6-403f-9749-c71cf2df6e45

module
public import Definitions.Def_GJKKL_Main_TrackParams
public import Definitions.Def_GJKKL_Numerics_Final
public import Definitions.Def_GJKKL_Main_Theorem
public import Theorems.Thm_GJKKL_mem_matchingsOfSize


set_option autoImplicit true
@[expose] public section
public section
open GJKKL GJKKL.Main
open Finset Real Pseudorandom GJKKL.Trajectory GJKKL.History GJKKL.Numerics
namespace GJKKL.Main
theorem _root_.solution {V : Type*} [DecidableEq V] (H : Finset (Finset V)) :
    (∅ : Finset (Finset V)) ∈ matchingsOfSize H 0 :=
  mem_matchingsOfSize.mpr ⟨empty_subset _, fun e he => absurd he (Finset.notMem_empty e),
    card_empty⟩
end GJKKL.Main
