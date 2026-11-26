-- Prove2me | solution 1 for FirstPassageLinearTransport.firstPassageLinearTransportOrbitCeiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:42:10.863472+00:00
-- url     : https://prove2.me/submissions/a4535686-3131-44a7-aa3b-186d5294f1a1

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_eventuallyShellOrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_le_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
import Theorems.Thm_FirstPassageLinearTransport_assembledBootstrap_naturalDensityOne_of_vanish
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_eventuallyOfEventuallyShellwise
import Theorems.Thm_FirstPassageLinearTransport_eventuallyShellClockLt6953
import Theorems.Thm_FirstPassageLinearTransport_eventuallyShellLanding
import Theorems.Thm_FirstPassageLinearTransport_exists_headlineScalars
import Theorems.Thm_FirstPassageLinearTransport_exists_stageSetup
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shellBootstrapRatioTendstoZero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_eq_orbit_stageClock
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
    {delta beta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1) (hbeta : 0 < beta) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            ∃ k : ℕ,
              (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
                (orbit k n : ℝ) ≤
                  Real.exp ((Real.log n) ^ (1 - delta)) ∧
                ∀ j : ℕ, j ≤ k →
                  (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta) := by
  let h : HeadlineScalars delta :=
    Classical.choice (exists_headlineScalars hdelta0 hdelta1)
  let eta := min ((h.r - a0) / 2) (beta / 2)
  have heta0 : 0 < eta := by
    dsimp [eta]
    exact lt_min (by linarith [h.a0_lt_r]) (by linarith)
  have hetaGap : eta < h.r - a0 := by
    have hle : eta ≤ (h.r - a0) / 2 := min_le_left _ _
    dsimp only [eta] at hle ⊢
    linarith [h.a0_lt_r]
  have hetaBeta : eta < beta := by
    have hle : eta ≤ beta / 2 := min_le_right _ _
    dsimp only [eta] at hle ⊢
    linarith
  let p : StageSetup h.r eta :=
    Classical.choice (exists_stageSetup h.a0_lt_r h.r_lt_one
      heta0 hetaGap)
  let Dc := quadraticWindowDensityRate eta
  have hDc0 : 0 < Dc := by
    dsimp [Dc]
    exact (extendedWindow_powerDense p).D_pos
  have hDc1 : Dc ≤ 1 := by
    dsimp [Dc]
    exact (extendedWindow_powerDense p).D_le_one
  have hchiDc : h.chi * Dc < 1 := by
    have hprod : h.chi * Dc ≤ h.chi * 1 :=
      mul_le_mul_of_nonneg_left hDc1 h.chi_pos.le
    nlinarith [h.chi_lt_r.trans h.r_lt_one]
  have hdensity : densityGamma h.omega h.chi < 1 := by
    simpa [densityGamma, one_div] using h.density_compat
  have hdescent : delta < descentAlpha h.omega h.r := by
    simpa [descentAlpha, one_div] using h.descent_compat
  let S := assembledBootstrap p h.omega
  have hSdense : NaturalDensityOne S :=
    assembledBootstrap_naturalDensityOne_of_vanish p h.omega
      (shellBootstrapRatioTendstoZero p h.chi_pos h.chi_lt_r
        h.chi_le_one hDc0 hDc1 le_rfl hchiDc h.omega_pos hdensity)
  have hlandingM := eventuallyShellLanding p h.omega_pos hdelta1 hdescent
  have hclockM := eventuallyShellClockLt6953 p h.r_lt_clock h.omega_pos
  have hceilingM := eventuallyShellOrbitCeiling p h.omega_pos hetaBeta
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageOrbit p (stageCount h.omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hclock := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageClock p (stageCount h.omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n) hclockM
  have hceiling := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      ∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) ^ (1 + beta)) hceilingM
  refine ⟨S, hSdense, ?_⟩
  filter_upwards [hlanding, hclock, hceiling,
    eventually_gt_atTop (0 : ℕ)] with n hnlanding hnclock hnceiling hnpos hnS
  have hnboot : n ∈ bootstrapSet p
      (stageCount h.omega (Nat.log 2 n)) := by
    exact hnS
  let k := stageClock p (stageCount h.omega (Nat.log 2 n)) n
  refine ⟨k, hnclock hnpos hnboot, ?_, hnceiling hnpos hnboot⟩
  rw [← stageOrbit_eq_orbit_stageClock]
  exact hnlanding hnpos hnboot
end FirstPassageLinearTransport
