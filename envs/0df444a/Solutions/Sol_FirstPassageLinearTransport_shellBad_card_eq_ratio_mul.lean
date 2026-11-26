-- Prove2me | solution 1 for FirstPassageLinearTransport.shellBad_card_eq_ratio_mul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:19:15.282579+00:00
-- url     : https://prove2.me/submissions/31eea726-55a9-4ce4-a3a3-08e2cded39b6

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (S : Set ℕ) (M : ℕ) :
    ((shellBad S M).card : ℝ) =
      shellExceptionalRatio S M * (2 : ℝ) ^ M := by
  unfold shellExceptionalRatio
  field_simp
end FirstPassageLinearTransport
