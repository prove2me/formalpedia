-- Prove2me | solution 1 for FirstPassageLinearTransport.PowerDense.C_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:56:42.220893+00:00
-- url     : https://prove2.me/submissions/87c0e087-1bef-4f13-8dd7-6d422b403b5c

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
    (h : PowerDense S C D) : 0 < C := h.1
end PowerDense
end FirstPassageLinearTransport
