-- Prove2me | solution 1 for Erdos1219.Ctx.pick_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:58.920663+00:00
-- url     : https://prove2.me/submissions/575463f7-a4c0-4344-b60e-18110b031c1f

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
import Theorems.Thm_Erdos1219_nonempty_of_mk_eq


set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)
namespace Erdos1219.Ctx
theorem _root_.solution (i : ℕ) : S.pick i ∈ S.Bu i :=
  Or.inl (nonempty_of_mk_eq (S.blocks_good i).mk1 (S.aleph0_le_μ i)).choose_spec
end Erdos1219.Ctx
