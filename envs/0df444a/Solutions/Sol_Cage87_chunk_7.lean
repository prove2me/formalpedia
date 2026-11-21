-- Prove2me | solution 1 for Cage87.chunk_7
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:47.566143+00:00
-- url     : https://prove2.me/submissions/87b756a8-336e-4c69-b494-6111816bf6c9

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution : verticesOk adj 672 96 = true := by decide +kernel
end Cage87
