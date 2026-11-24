-- Prove2me | solution 1 for Erdos1219.Ctx.B_basic
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:58.413515+00:00
-- url     : https://prove2.me/submissions/d434e2af-8cee-4c81-8c12-c358c62f139b

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)
namespace Erdos1219.Ctx
theorem _root_.solution (k : ℕ) : S.Basic k (S.B k) := (S.blocks k).2
end Erdos1219.Ctx
