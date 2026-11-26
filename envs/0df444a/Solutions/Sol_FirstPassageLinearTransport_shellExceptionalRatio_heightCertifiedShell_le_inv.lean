-- Prove2me | solution 1 for FirstPassageLinearTransport.shellExceptionalRatio_heightCertifiedShell_le_inv
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:52.074242+00:00
-- url     : https://prove2.me/submissions/30a39651-2925-4592-9ee7-d989188ee7b3

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_heightCertifiedShell_le
import Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellMultiplicativeHit_quarter_le


set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta omega zeta alpha : ℝ} (p : StageSetup r eta) (M : ℕ) :
    shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
      shellExceptionalRatio (shellBootstrap p omega M) M +
        4 / stretchedHeightShellAllowance zeta alpha M := by
  have hbase := shellExceptionalRatio_heightCertifiedShell_le
    (omega := omega) (zeta := zeta) (alpha := alpha) p M
  have hhit := normalized_card_shellMultiplicativeHit_quarter_le
    (R := stretchedHeightShellAllowance zeta alpha M)
    (Real.exp_pos _) M
  exact hbase.trans (add_le_add (le_refl _) hhit)
end FirstPassageLinearTransport
