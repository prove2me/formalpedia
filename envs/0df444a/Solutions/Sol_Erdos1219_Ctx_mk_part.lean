-- Prove2me | solution 1 for Erdos1219.Ctx.mk_part
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:49:13.409643+00:00
-- url     : https://prove2.me/submissions/503d68b3-99f3-4be5-b4ad-c9a0963dd2bd

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
theorem _root_.solution (δ : Bool) (k : ℕ) : #(S.part δ k) = S.μ k := by
  cases δ
  · exact (S.blocks_good k).mk1
  · exact (S.blocks_good k).mk2
end Erdos1219.Ctx
