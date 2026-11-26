-- Prove2me | solution 1 for FirstPassageLinearTransport.PowerDense.D_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:42.821441+00:00
-- url     : https://prove2.me/submissions/fdde4fbe-6a39-4ace-8b13-c31d909b1096

import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Definitions.Def_FirstPassageLinearTransport_Basic
import Definitions.Def_FirstPassageLinearTransport_Density

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace PowerDense
theorem _root_.solution {S : Set ℕ} {C D : ℝ}
    (h : PowerDense S C D) : D ≤ 1 := h.2.2.1
end PowerDense
end FirstPassageLinearTransport
