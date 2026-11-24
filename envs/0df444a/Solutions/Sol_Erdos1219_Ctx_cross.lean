-- Prove2me | solution 1 for Erdos1219.Ctx.cross
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:50:33.107023+00:00
-- url     : https://prove2.me/submissions/22e05925-6591-4052-8d33-cec7692282b3

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
import Theorems.Thm_Erdos1219_Ctx_mem_prevU_B
import Theorems.Thm_Erdos1219_Ctx_canonical
import Theorems.Thm_Erdos1219_Ctx_pick_mem

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)
namespace Erdos1219.Ctx
theorem _root_.solution {i j : ℕ} (hij : i < j) {a b : V} (ha : a ∈ S.Bu i) (hb : b ∈ S.Bu j) :
    S.f a b = S.g i j := by
  have hj := (S.blocks_good j).cls
  calc S.f a b = S.f (S.pick i) b := S.canonical hij ha (S.pick_mem i) hb
    _ = S.f b (S.pick i) := S.hf _ _
    _ = S.f (S.guide j) (S.pick i) := hj b hb _ (S.mem_prevU_B hij (S.pick_mem i))
    _ = S.f (S.pick i) (S.guide j) := S.hf _ _
end Erdos1219.Ctx
