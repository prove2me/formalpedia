-- Prove2me | solution 1 for Erdos266.tSeq_bijective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:40:27.897795+00:00
-- url     : https://prove2.me/submissions/baa4d835-f999-47d3-b204-9cec20666977

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
public import Theorems.Thm_Erdos266_tSeq_injective
public import Theorems.Thm_Erdos266_tSeq_surjective

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution : Function.Bijective tSeq :=
  ⟨tSeq_injective, tSeq_surjective⟩
end Erdos266
