-- Prove2me | solution 1 for Champernowne.champM_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:36:51.954956+00:00
-- url     : https://prove2.me/submissions/78381a6b-9462-47e1-bb94-4aad085a8fa2

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
theorem _root_.solution (b n : ℕ) : 0 < champM b n := Nat.succ_pos _
end Champernowne
