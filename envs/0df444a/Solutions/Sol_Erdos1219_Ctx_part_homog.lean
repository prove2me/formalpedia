-- Prove2me | solution 1 for Erdos1219.Ctx.part_homog
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:59.934857+00:00
-- url     : https://prove2.me/submissions/ef70ca92-2276-490b-968d-00eb7f2a8c33

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
theorem _root_.solution (δ : Bool) (k : ℕ) : Homog S.f δ (S.part δ k) := by
  cases δ
  · exact (S.blocks_good k).hom1
  · exact (S.blocks_good k).hom2
end Erdos1219.Ctx
