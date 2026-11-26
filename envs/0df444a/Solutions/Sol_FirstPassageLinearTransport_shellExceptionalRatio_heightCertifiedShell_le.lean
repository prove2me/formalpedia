-- Prove2me | solution 1 for FirstPassageLinearTransport.shellExceptionalRatio_heightCertifiedShell_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:44.134324+00:00
-- url     : https://prove2.me/submissions/344fff00-96d3-4163-b851-237dab0cf907

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_shellBad_heightCertifiedShell_subset

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
        ((shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4)).card : ℝ) /
            (2 : ℝ) ^ M := by
  have hsub := shellBad_heightCertifiedShell_subset
    (omega := omega) (zeta := zeta) (alpha := alpha) p M
  have hcardNat := Finset.card_le_card hsub
  have hunion := Finset.card_union_le
    (shellBad (shellBootstrap p omega M) M)
    (shellMultiplicativeHit M
      (stretchedHeightShellAllowance zeta alpha M / 4))
  have hcard :
      ((shellBad (heightCertifiedShell p omega zeta alpha M) M).card : ℝ) ≤
        (shellBad (shellBootstrap p omega M) M).card +
          (shellMultiplicativeHit M
            (stretchedHeightShellAllowance zeta alpha M / 4)).card := by
    exact_mod_cast hcardNat.trans hunion
  have hpow : 0 < (2 : ℝ) ^ M := by positivity
  unfold shellExceptionalRatio
  calc
    ((shellBad (heightCertifiedShell p omega zeta alpha M) M).card : ℝ) /
        (2 : ℝ) ^ M ≤
      (((shellBad (shellBootstrap p omega M) M).card : ℝ) +
        (shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4)).card) /
          (2 : ℝ) ^ M :=
      div_le_div_of_nonneg_right hcard hpow.le
    _ = ((shellBad (shellBootstrap p omega M) M).card : ℝ) /
          (2 : ℝ) ^ M +
        ((shellMultiplicativeHit M
          (stretchedHeightShellAllowance zeta alpha M / 4)).card : ℝ) /
            (2 : ℝ) ^ M := add_div _ _ _
end FirstPassageLinearTransport
