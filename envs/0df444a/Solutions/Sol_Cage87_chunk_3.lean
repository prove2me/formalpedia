-- Prove2me | solution 1 for Cage87.chunk_3
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T20:24:04.95582+00:00
-- url     : https://prove2.me/submissions/ed63af8a-923d-4193-9993-cce03301a5bf

module
public import Definitions.Def_Cage87_Check
public import Definitions.Def_Cage87_Data
public import Definitions.Def_Cage87_Chunks

set_option autoImplicit true
@[expose] public section
public section
open Cage87
namespace Cage87
theorem _root_.solution : verticesOk adj 288 96 = true := by decide +kernel
end Cage87
