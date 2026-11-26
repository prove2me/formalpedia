-- Prove2me | solution 1 for FirstPassageLinearTransport.naturalDensityOne_of_sharpMovingShellErrorWithHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:02:44.588435+00:00
-- url     : https://prove2.me/submissions/7b7e37b8-a092-4a01-9a00-090db60cc28d

import Definitions.Def_FirstPassageLinearTransport_ShrinkingParameters
import Definitions.Def_FirstPassageLinearTransport_VaryingDensity
import Definitions.Def_FirstPassageLinearTransport_MovingEndpointScalars
import Theorems.Thm_FirstPassageLinearTransport_tendsto_sharpMovingShellErrorWithHeight_zero
import Theorems.Thm_FirstPassageLinearTransport_naturalDensityOne_assembleDyadic
import Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_nonneg


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (S : ℕ → Set ℕ) {A R : ℕ → ℝ} {C eps : ℝ}
    (heps : 0 < eps)
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop)
    (hR : Tendsto R atTop atTop)
    (hShell : ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (S M) M ≤
        C * ((2 : ℝ) ^ (-(sharpMovingRankBuffer A M)) +
          (((M : ℝ) + 2) ^ (-eps))) + 4 / R M) :
    NaturalDensityOne (assembleDyadic S) := by
  apply naturalDensityOne_assembleDyadic S
  apply squeeze_zero'
  · exact Eventually.of_forall fun M => shellExceptionalRatio_nonneg (S M) M
  · exact hShell
  · exact tendsto_sharpMovingShellErrorWithHeight_zero hbuffer heps hR
end FirstPassageLinearTransport
