-- Prove2me | solution 1 for Eidos.Examples.Reserve.repaired_rejects_counterexample
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-20T23:36:59.201692+00:00
-- url     : https://prove2.me/submissions/e2c13cf1-2247-44e2-9735-e818dcb47a3c

import Definitions.Def_Eidos_Ergo_Expr
import Definitions.Def_Eidos_Examples_Reserve

set_option autoImplicit false
open Eidos Eidos.Examples Eidos.Examples.Reserve
open Ergo
namespace Eidos.Examples.Reserve
theorem _root_.solution :
    ¬ Accepts (script exampleReserve) attackContext := by decide
end Eidos.Examples.Reserve
