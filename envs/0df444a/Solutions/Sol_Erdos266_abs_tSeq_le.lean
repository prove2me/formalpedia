-- Prove2me | solution 1 for Erdos266.abs_tSeq_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:20.331641+00:00
-- url     : https://prove2.me/submissions/a3de381a-f961-4787-abbc-6717314bda96

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution (i : ℕ) : |tSeq i| ≤ (i : ℚ) + 1 :=
  (Nat.find_spec (exists_fresh i (picks i))).2
end Erdos266
