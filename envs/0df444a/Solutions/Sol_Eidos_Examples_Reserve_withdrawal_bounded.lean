-- Prove2me | solution 1 for Eidos.Examples.Reserve.withdrawal_bounded
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:37:27.344217+00:00
-- url     : https://prove2.me/submissions/4b26be2a-273f-450f-bc24-986e933f94bd

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve
import Theorems.Thm_Eidos_Examples_Reserve_accepts_iff

set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo
namespace Eidos.Examples.Reserve
theorem _root_.solution (reserve : Long) (ctx : Context)
    (accepted : Accepts (script reserve) ctx) : WithdrawalBounded reserve ctx := by
  obtain ⟨out, hout, hself, hreserve⟩ := (accepts_iff reserve ctx).1 accepted
  exact ⟨out, hout, by omega, by omega⟩
end Eidos.Examples.Reserve
