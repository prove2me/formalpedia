-- Prove2me | solution 1 for Champernowne.tendsto_champIndex_atTop
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:39:41.014457+00:00
-- url     : https://prove2.me/submissions/ca5b69fc-e0b1-4055-a7ea-a5c58e938996

module
public import Definitions.Def_LeanPool_Champernowne_Positions
public import Mathlib.Analysis.Asymptotics.Lemmas
public import Mathlib.Analysis.SpecificLimits.Basic
public import Definitions.Def_LeanPool_Champernowne_Asymptotics

set_option autoImplicit true
@[expose] public section
public section
open Champernowne
open Filter Asymptotics Topology
namespace Champernowne
theorem _root_.solution (b : ℕ) :
    Tendsto (champIndex b) atTop atTop := by
  rw [Filter.tendsto_atTop]
  intro K
  filter_upwards [Filter.eventually_ge_atTop ((champBlocks b K).length)]
    with n hn
  exact Nat.le_findGreatest (le_trans (le_length_champBlocks b K) hn) hn
end Champernowne
