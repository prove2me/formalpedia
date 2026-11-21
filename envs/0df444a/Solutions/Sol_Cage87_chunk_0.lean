-- Prove2me | solution 1 for Cage87.chunk_0
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:50.521372+00:00
-- url     : https://prove2.me/submissions/320f34f1-c63d-4c27-9e5e-c899e79de3a5

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution : verticesOk adj 0 96 = true := by decide +kernel
end Cage87
