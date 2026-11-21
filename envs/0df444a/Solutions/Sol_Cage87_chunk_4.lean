-- Prove2me | solution 1 for Cage87.chunk_4
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:05.46859+00:00
-- url     : https://prove2.me/submissions/0bcd900a-6d35-4b78-8ac4-5e4c568ab1e3

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution : verticesOk adj 384 96 = true := by decide +kernel
end Cage87
