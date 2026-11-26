-- Prove2me | solution 1 for FirstPassageLinearTransport.parityDigitR_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:22:59.91987+00:00
-- url     : https://prove2.me/submissions/dc09d939-da38-49d3-befc-bf0815314a0a

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (n i : ℕ) : parityDigitR n i ≤ 1 := by
  unfold parityDigitR
  exact_mod_cast (show (parityBit n i : ℕ) ≤ 1 by omega)
end FirstPassageLinearTransport
