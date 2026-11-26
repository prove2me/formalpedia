-- Prove2me | solution 1 for FirstPassageLinearTransport.normalizedCorrectionTerm_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:23:29.15023+00:00
-- url     : https://prove2.me/submissions/cbc2fe01-11ae-446f-8636-f07b9dc9c04e

import Mathlib.Algebra.Ring.GeomSum
import Definitions.Def_FirstPassageLinearTransport_Barrier
import Definitions.Def_FirstPassageLinearTransport_Envelope
import Theorems.Thm_FirstPassageLinearTransport_parityDigitR_nonneg

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (k n i : ℕ) :
    0 ≤ normalizedCorrectionTerm k n i := by
  unfold normalizedCorrectionTerm
  exact div_nonneg (parityDigitR_nonneg n i) (by positivity)
end FirstPassageLinearTransport
