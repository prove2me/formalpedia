-- Prove2me | solution 1 for Erdos266.picks_succ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:33:17.32742+00:00
-- url     : https://prove2.me/submissions/d3e2c193-f456-4132-acf6-ce7765f08d2b

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution (i : ℕ) : picks (i + 1) = picks i ++ [tSeq i] := rfl
end Erdos266
