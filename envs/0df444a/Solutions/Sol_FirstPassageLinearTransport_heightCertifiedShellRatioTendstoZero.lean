-- Prove2me | solution 1 for FirstPassageLinearTransport.heightCertifiedShellRatioTendstoZero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:00.667931+00:00
-- url     : https://prove2.me/submissions/48cf8349-bf0d-45a1-8f1f-03be8bc4393b

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_heightCertifiedShell_le_inv
import Theorems.Thm_FirstPassageLinearTransport_tendsto_four_div_stretchedHeightShellAllowance_zero
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellBootstrapRatioTendstoZero
import Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_nonneg
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {r eta chi Dc omega zeta alpha : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega : 0 < omega)
    (hdensity : densityGamma omega chi < 1)
    (hzeta : 0 < zeta) (halpha : 0 < alpha) :
    Tendsto (fun M => shellExceptionalRatio
      (heightCertifiedShell p omega zeta alpha M) M) atTop (nhds 0) := by
  have hboot := shellBootstrapRatioTendstoZero p
    hchi0 hchir hchi1 hDc0 hDc1 hDcRate hchiDc homega hdensity
  have hheight :=
    tendsto_four_div_stretchedHeightShellAllowance_zero hzeta halpha
  have hsum := hboot.add hheight
  have hsum0 : Tendsto (fun M =>
      shellExceptionalRatio (shellBootstrap p omega M) M +
        4 / stretchedHeightShellAllowance zeta alpha M) atTop (nhds 0) := by
    simpa using hsum
  have hupper : ∀ M : ℕ,
      shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
        shellExceptionalRatio (shellBootstrap p omega M) M +
          4 / stretchedHeightShellAllowance zeta alpha M :=
    shellExceptionalRatio_heightCertifiedShell_le_inv p
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
    tendsto_const_nhds hsum0
  · filter_upwards with M
    exact shellExceptionalRatio_nonneg _ _
  · filter_upwards with M
    exact hupper M
end FirstPassageLinearTransport
