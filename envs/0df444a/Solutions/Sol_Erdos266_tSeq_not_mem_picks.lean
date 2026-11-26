-- Prove2me | solution 1 for Erdos266.tSeq_not_mem_picks
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:19.465649+00:00
-- url     : https://prove2.me/submissions/c1521301-5857-4275-b2d8-9eb53ba6a804

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution (i : ℕ) : tSeq i ∉ picks i :=
  (Nat.find_spec (exists_fresh i (picks i))).1
end Erdos266
