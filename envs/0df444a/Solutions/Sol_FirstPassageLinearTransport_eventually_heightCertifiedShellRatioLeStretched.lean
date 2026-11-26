-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_heightCertifiedShellRatioLeStretched
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:41:50.872973+00:00
-- url     : https://prove2.me/submissions/1ec4b2a7-efd4-4e52-902e-282c5177454c

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_shellExceptionalRatio_heightCertifiedShell_le_inv
import Theorems.Thm_FirstPassageLinearTransport_eventually_four_div_stretchedHeightShellAllowance_le_stretched
import Theorems.Thm_FirstPassageLinearTransport_QuantitativeDensity_stretchedShellScale_pos
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_eventuallyShellBootstrapRatioLeStretched
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
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
    {r eta chi Dc omega zeta alpha sigma : ℝ} (p : StageSetup r eta)
    (hchi0 : 0 < chi) (hchir : chi < r) (hchi1 : chi ≤ 1)
    (hDc0 : 0 < Dc) (hDc1 : Dc ≤ 1)
    (hDcRate : Dc ≤ quadraticWindowDensityRate eta)
    (hchiDc : chi * Dc < 1)
    (homega0 : 0 < omega)
    (hzeta : 0 < zeta)
    (halpha0 : 0 < alpha)
    (hsigma0 : 0 < sigma) (hsigmaAlpha : sigma ≤ alpha)
    (hsigmaDensity : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ M : ℕ in atTop,
      shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
        6 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
  obtain ⟨cBoot, hcBoot, hboot⟩ :=
    eventuallyShellBootstrapRatioLeStretched p
      hchi0 hchir hchi1 hDc0 hDc1 hDcRate hchiDc homega0
      hsigma0 hsigmaDensity
  let cHeight := zeta * (Real.log 2 / 2) ^ alpha
  have hcHeight : 0 < cHeight := by
    dsimp [cHeight]
    positivity
  let c := min cBoot cHeight
  have hc : 0 < c := lt_min hcBoot hcHeight
  have hheight :=
    eventually_four_div_stretchedHeightShellAllowance_le_stretched
      hzeta halpha0 hsigmaAlpha
  refine ⟨c, hc, ?_⟩
  filter_upwards [hboot, hheight] with M hbootM hheightM
  have hscale0 :
      0 ≤ (QuantitativeDensity.stretchedShellScale M) ^ sigma :=
    Real.rpow_nonneg
      (QuantitativeDensity.stretchedShellScale_pos M).le _
  have hcBootLe : c ≤ cBoot := min_le_left _ _
  have hcHeightLe : c ≤ cHeight := min_le_right _ _
  have hbootExp :
      Real.exp
          (-cBoot * (QuantitativeDensity.stretchedShellScale M) ^ sigma) ≤
        Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
    apply Real.exp_le_exp.2
    nlinarith
  have hheightExp :
      Real.exp
          (-cHeight * (QuantitativeDensity.stretchedShellScale M) ^ sigma) ≤
        Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by
    apply Real.exp_le_exp.2
    nlinarith
  calc
    shellExceptionalRatio (heightCertifiedShell p omega zeta alpha M) M ≤
        shellExceptionalRatio (shellBootstrap p omega M) M +
          4 / stretchedHeightShellAllowance zeta alpha M :=
      shellExceptionalRatio_heightCertifiedShell_le_inv p M
    _ ≤ 2 * Real.exp
          (-cBoot * (QuantitativeDensity.stretchedShellScale M) ^ sigma) +
        4 * Real.exp
          (-cHeight * (QuantitativeDensity.stretchedShellScale M) ^ sigma) :=
      add_le_add hbootM hheightM
    _ ≤ 2 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) +
        4 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) :=
      add_le_add
        (mul_le_mul_of_nonneg_left hbootExp (by norm_num))
        (mul_le_mul_of_nonneg_left hheightExp (by norm_num))
    _ = 6 * Real.exp
          (-c * (QuantitativeDensity.stretchedShellScale M) ^ sigma) := by ring
end FirstPassageLinearTransport
