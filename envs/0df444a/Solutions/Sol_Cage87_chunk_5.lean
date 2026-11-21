-- Prove2me | solution 1 for Cage87.chunk_5
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:06.062078+00:00
-- url     : https://prove2.me/submissions/4b94b714-09ef-45a0-994f-5b656ebdfda2

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution : verticesOk adj 480 96 = true := by decide +kernel
end Cage87
