-- Prove2me | solution 1 for FirstPassageLinearTransport.shellExceptionalRatio_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:17:05.055824+00:00
-- url     : https://prove2.me/submissions/19adbfd5-0c47-4439-8caf-1e7f3572837a

import Definitions.Def_FirstPassageLinearTransport_Density
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real Topology BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution (S : Set ℕ) (M : ℕ) :
    0 ≤ shellExceptionalRatio S M := by
  unfold shellExceptionalRatio
  positivity
end FirstPassageLinearTransport
