-- Prove2me | solution 1 for Cage87.wf_ok
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:36.902151+00:00
-- url     : https://prove2.me/submissions/25cce152-c3de-43bc-bfbf-1b7d6a6b7a8b

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution : wfOk adj 768 8 = true := by decide +kernel
end Cage87
