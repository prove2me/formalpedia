-- Prove2me | solution 1 for Erdos1219.Ctx.part_subset_Bu
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:59.326795+00:00
-- url     : https://prove2.me/submissions/dd096868-60e2-4410-9ffa-51d88f00168b

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
theorem _root_.solution (δ : Bool) (k : ℕ) : S.part δ k ⊆ S.Bu k := by
  cases δ
  · exact fun a ha => Or.inl ha
  · exact fun a ha => Or.inr ha
end Erdos1219.Ctx
