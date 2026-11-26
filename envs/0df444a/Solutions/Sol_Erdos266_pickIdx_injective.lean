-- Prove2me | solution 1 for Erdos266.pickIdx_injective
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T02:37:33.342951+00:00
-- url     : https://prove2.me/submissions/5bb9a4f9-bc36-46a5-9ed9-16a538ba8113

module
public import Mathlib
public import Definitions.Def_Erdos266_Enumeration
public import Theorems.Thm_Erdos266_tSeq_injective

set_option autoImplicit false
@[expose] public section
public section
open Erdos266
namespace Erdos266
theorem _root_.solution : Function.Injective pickIdx := fun _ _ hab =>
  tSeq_injective (congrArg qEnum hab)
end Erdos266
