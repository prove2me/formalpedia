-- Prove2me | solution 1 for Erdos266.newS_eq_blk
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:58:55.130956+00:00
-- url     : https://prove2.me/submissions/a5de9847-4b7a-4661-96a8-b1412fbace1e

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset
namespace Erdos266
theorem _root_.solution {k : ℕ} {st : AlgSt} (h : Inv k st) {j : ℕ} (hj : j < dOf k) :
    newS k st h k j = blk k st h ⟨j, hj⟩ := by
  rw [newS, if_pos rfl, dif_pos hj]
end Erdos266
