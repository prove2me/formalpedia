-- Prove2me | solution 1 for Erdos1219.Ctx.canonical
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:49:35.189315+00:00
-- url     : https://prove2.me/submissions/59927c25-ad1c-400b-b69c-c59a978c0fa6

import Definitions.Def_Erdos1219_Defs
import Definitions.Def_Erdos1219_CardinalLemmas
import Definitions.Def_Erdos1219_Ramsey
import Definitions.Def_Erdos1219_UnbalancedErdosRado
import Definitions.Def_Erdos1219_Canonization
import Theorems.Thm_Erdos1219_Ctx_mem_prevU_B

set_option autoImplicit false
open Cardinal Ordinal Function
open Erdos1219
universe u
open Erdos1219.Ctx
variable {V : Type u} (S : Ctx V)
namespace Erdos1219.Ctx
theorem _root_.solution {i j : ℕ} (hij : i < j) {a a' b : V} (ha : a ∈ S.Bu i) (ha' : a' ∈ S.Bu i)
    (hb : b ∈ S.Bu j) : S.f a b = S.f a' b := by
  have hj := (S.blocks_good j).cls
  have hi := (S.blocks_good i).same
  calc S.f a b = S.f b a := S.hf a b
    _ = S.f (S.guide j) a := hj b hb a (S.mem_prevU_B hij ha)
    _ = S.f a (S.guide j) := S.hf _ _
    _ = S.f a' (S.guide j) := hi a ha a' ha' j
    _ = S.f (S.guide j) a' := S.hf _ _
    _ = S.f b a' := (hj b hb a' (S.mem_prevU_B hij ha')).symm
    _ = S.f a' b := S.hf _ _
end Erdos1219.Ctx
