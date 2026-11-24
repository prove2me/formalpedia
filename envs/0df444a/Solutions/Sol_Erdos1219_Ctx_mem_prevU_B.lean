-- Prove2me | solution 1 for Erdos1219.Ctx.mem_prevU_B
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T05:48:56.313827+00:00
-- url     : https://prove2.me/submissions/4f59ade0-dd15-48a0-bae0-ade3815339f7

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
theorem _root_.solution {i j : ℕ} (hij : i < j) {a : V} (ha : a ∈ S.Bu i) :
    a ∈ S.prevU j (fun i _ => S.B i) :=
  S.mem_prevU.2 ⟨i, hij, ha⟩
end Erdos1219.Ctx
