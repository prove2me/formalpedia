-- Prove2me | solution 1 for FirstPassageLinearTransport.heightCertifiedExceptionalCountEventually
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:59.63183+00:00
-- url     : https://prove2.me/submissions/3b99c580-77c5-486e-8426-06d8c3739ffc

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_eventually_heightCertifiedShellRatioLeStretched
import Theorems.Thm_FirstPassageLinearTransport_QuantitativeDensity_badCount_assembleDyadic_le_stretched_log
import Theorems.Thm_FirstPassageLinearTransport_QuantitativeDensity_stretchedDyadicRate_pos
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
    (hsigma0 : 0 < sigma) (hsigma1 : sigma ≤ 1)
    (hsigmaAlpha : sigma ≤ alpha)
    (hsigmaDensity : sigma < 1 - densityGamma omega chi) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℕ in atTop,
      (badCount (assembledHeightCertified p omega zeta alpha) X : ℝ) ≤
        13 * X * Real.exp (-c * (Real.log X) ^ sigma) := by
  obtain ⟨c0, hc0, hratio⟩ :=
    eventually_heightCertifiedShellRatioLeStretched p
      hchi0 hchir hchi1 hDc0 hDc1 hDcRate hchiDc homega0
      hzeta halpha0 hsigma0 hsigmaAlpha hsigmaDensity
  obtain ⟨M0, hM0⟩ := eventually_atTop.1 hratio
  let c := QuantitativeDensity.stretchedDyadicRate c0 / 2
  have hc : 0 < c := by
    dsimp [c]
    exact div_pos (QuantitativeDensity.stretchedDyadicRate_pos hc0) (by norm_num)
  refine ⟨c, hc, ?_⟩
  filter_upwards [eventually_ge_atTop (2 ^ (2 * M0 + 2))] with X hX
  have hX0 : 0 < X := by
    have hp : 0 < 2 ^ (2 * M0 + 2) := by positivity
    omega
  have hlogLower : 2 * M0 + 2 ≤ Nat.log 2 X :=
    Nat.le_log_of_pow_le (by norm_num) hX
  have hL2 : 2 ≤ Nat.log 2 X := by omega
  have hMhalf : M0 ≤ (Nat.log 2 X) / 2 := by omega
  have hbound :=
    QuantitativeDensity.badCount_assembleDyadic_le_stretched_log
      (heightCertifiedShell p omega zeta alpha) M0 X 6 c0 sigma
      (by norm_num) hc0 hsigma0 hsigma1
      (fun M hM => hM0 M hM) hX0 hL2 hMhalf
  change (badCount (assembleDyadic
      (heightCertifiedShell p omega zeta alpha)) X : ℝ) ≤
    13 * X * Real.exp
      (-(QuantitativeDensity.stretchedDyadicRate c0 / 2) *
        (Real.log X) ^ sigma)
  norm_num at hbound
  simpa only [neg_mul] using hbound
end FirstPassageLinearTransport
