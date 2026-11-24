-- Prove2me | solution 1 for Erdos1219.Ctx.Bu_subset_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:49:45.988816+00:00
-- url     : https://prove2.me/submissions/b2be6022-51e9-4ae6-a0d4-4de6f5da0c44

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
import Theorems.Thm_Erdos1219_Ctx_B_basic

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)
namespace Erdos1219.Ctx
theorem _root_.solution (k : ℕ) : S.Bu k ⊆ S.A k := (S.B_basic k).sub
end Erdos1219.Ctx
