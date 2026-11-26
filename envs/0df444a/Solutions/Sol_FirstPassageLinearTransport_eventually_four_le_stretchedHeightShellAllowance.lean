-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_four_le_stretchedHeightShellAllowance
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:57:32.707436+00:00
-- url     : https://prove2.me/submissions/779cf9c8-35de-4c14-bc77-4ad8bc0aa267

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_tendsto_stretchedHeightShellAllowance_atTop

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {zeta alpha : ℝ} (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    ∀ᶠ M : ℕ in atTop, 4 ≤ stretchedHeightShellAllowance zeta alpha M :=
  (tendsto_atTop.1
    (tendsto_stretchedHeightShellAllowance_atTop hzeta halpha)) 4
end FirstPassageLinearTransport
