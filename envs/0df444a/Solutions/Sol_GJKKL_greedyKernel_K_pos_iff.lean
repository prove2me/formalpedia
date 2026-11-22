-- Prove2me | solution 1 for GJKKL.greedyKernel_K_pos_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:49:36.829814+00:00
-- url     : https://prove2.me/submissions/3a2e36f9-241f-4078-b9b8-beb0da13d6ae

module
public import Definitions.Def_GJKKL_History_Basic
public import Definitions.Def_GJKKL_Statement
public import Definitions.Def_GJKKL_Greedy_Process
public import Theorems.Thm_GJKKL_greedyKernel_K

set_option autoImplicit true
@[expose] public section
public section
open GJKKL
open Finset Pseudorandom History
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace GJKKL
theorem _root_.solution {H : Finset (Finset V)} {h : List (Finset V)} {a : Finset V} :
    0 < (greedyKernel H).K h a ↔ a ∈ avail H h := by
  rw [greedyKernel_K]
  constructor
  · intro hpos
    by_contra ha
    rw [if_neg ha] at hpos
    exact lt_irrefl _ hpos
  · intro ha
    rw [if_pos ha]
    have : 0 < (avail H h).card := card_pos.mpr ⟨a, ha⟩
    positivity
end GJKKL
