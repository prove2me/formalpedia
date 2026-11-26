-- Prove2me | solution 1 for FriedCrossing.TorsionCore.N_C_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:22.827589+00:00
-- url     : https://prove2.me/submissions/9348e059-8f24-4190-81aa-49bb70c32132

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution : (N_C : ℤ) = (1 * (1 + 1) + 2 * (2 - 1) + 1 * (1 + 1) + 0) / 2 := by
  decide
end FriedCrossing.TorsionCore
