-- Prove2me | solution 1 for FriedCrossing.TorsionCore.m_C_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T05:08:48.145235+00:00
-- url     : https://prove2.me/submissions/977ad790-5474-455b-b666-2dc28b3d8964

import Definitions.Def_B1s_fried_statement_defs_9_14
import Definitions.Def_B1s_fried_crossing_9_03

set_option autoImplicit true
set_option linter.style.header false
open FriedCrossing
open Filter Topology Matrix
open FriedCrossing.TorsionCore
variable {K : Type*} [Field K]
namespace FriedCrossing.TorsionCore
theorem _root_.solution : (m_C : ℤ) = (0 + 1 * (1 - 1) + 3 * (3 + 1)) / 2 := by
  decide
end FriedCrossing.TorsionCore
