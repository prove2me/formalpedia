-- Prove2me | solution 1 for Cage87.chunk_1
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:23:51.257671+00:00
-- url     : https://prove2.me/submissions/7583619f-652e-4f53-b769-219ffdb87364

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution : verticesOk adj 96 96 = true := by decide +kernel
end Cage87
