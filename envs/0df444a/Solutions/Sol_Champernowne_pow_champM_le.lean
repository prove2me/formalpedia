-- Prove2me | solution 1 for Champernowne.pow_champM_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T21:37:01.369174+00:00
-- url     : https://prove2.me/submissions/75a65385-0500-4194-8042-aad4f58c4624

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
theorem _root_.solution (b n : ℕ) :
    b ^ (champM b n - 1) ≤ champIndex b n + 1 := by
  rw [champM, Nat.add_sub_cancel]
  exact Nat.pow_log_le_self b (Nat.succ_ne_zero _)
end Champernowne
