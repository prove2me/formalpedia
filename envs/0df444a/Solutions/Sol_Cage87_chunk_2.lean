-- Prove2me | solution 1 for Cage87.chunk_2
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:51.883321+00:00
-- url     : https://prove2.me/submissions/1caf8459-bd69-4090-877d-1a0f8791430a

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution : verticesOk adj 192 96 = true := by decide +kernel
end Cage87
