-- Prove2me | solution 1 for FirstPassageLinearTransport.stretchedLogCommonLandingWithRelativeHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:44:14.545039+00:00
-- url     : https://prove2.me/submissions/d685f3fa-c6ce-48b8-b1b6-1a95bb6540c4

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_eventuallyShellBootstrapRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_assembledHeightCertified_naturalDensityOne
import Theorems.Thm_FirstPassageLinearTransport_exists_rawClockHeightStage
import Theorems.Thm_FirstPassageLinearTransport_stretchedHeightShellAllowance_le_source
import Theorems.Thm_FirstPassageLinearTransport_eventually_four_le_stretchedHeightShellAllowance
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_le_one
import Theorems.Thm_FirstPassageLinearTransport_PowerDense_D_pos
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
import Theorems.Thm_FirstPassageLinearTransport_eventuallyShellRawClockLt
import Theorems.Thm_FirstPassageLinearTransport_extendedWindow_powerDense
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell_log
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_eq_orbit
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
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
    {delta zeta : ℝ}
    (hdelta0 : 0 < delta) (hdelta1 : delta < 1)
    (hzeta : 0 < zeta) :
    ∃ S : Set ℕ,
      NaturalDensityOne S ∧
        ∀ᶠ n : ℕ in atTop,
          n ∈ S →
            ∃ k ell : ℕ,
              (k : ℝ) < (6953 / 1000 : ℝ) * Real.log n ∧
              (ell : ℝ) < (261 / 25 : ℝ) * Real.log n ∧
              orbit k n = rawOrbit ell n ∧
              (orbit k n : ℝ) ≤
                Real.exp ((Real.log n) ^ (1 - delta)) ∧
              (∀ j : ℕ, j ≤ k →
                (orbit j n : ℝ) ≤
                  (n : ℝ) * Real.exp
                    (zeta * (Real.log n) ^ (1 - delta))) ∧
              (∀ i : ℕ, i ≤ ell →
                (rawOrbit i n : ℝ) ≤
                  (n : ℝ) * Real.exp
                    (zeta * (Real.log n) ^ (1 - delta))) := by
  obtain ⟨h, eta, p, hetaGap, hrawLeading, hre⟩ :=
    exists_rawClockHeightStage hdelta0 hdelta1
  let alpha := 1 - delta
  have halpha : 0 < alpha := by dsimp [alpha]; linarith
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
  let S := assembledHeightCertified p h.omega zeta alpha
  have hSdense : NaturalDensityOne S :=
    assembledHeightCertified_naturalDensityOne p
      h.chi_pos h.chi_lt_r h.chi_le_one hDc0 hDc1 le_rfl hchiDc
      h.omega_pos hdensity hzeta halpha
  have hlandingM := eventuallyShellLanding p h.omega_pos hdelta1 hdescent
  have hclockM := eventuallyShellClockLt6953 p h.r_lt_clock h.omega_pos
  have hrawM := eventuallyShellRawClockLt p h.omega_pos hrawLeading
  have hheightCore :=
    eventuallyShellBootstrapRelativeHeight p h.omega_pos hre.le
  have hH4 := eventually_four_le_stretchedHeightShellAllowance hzeta halpha
  have hheightM : ∀ᶠ M : ℕ in atTop, ∀ n : ℕ,
      0 < n → n ∈ dyadicShell M →
      n ∈ heightCertifiedShell p h.omega zeta alpha M →
      (∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M / 2) ∧
      (∀ i : ℕ,
        i ≤ rawTime n (stageClock p (stageCount h.omega M) n) →
        (rawOrbit i n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M) := by
    filter_upwards [hheightCore, hH4] with M hheight hH
    intro n hn hnshell hncert
    exact hheight n (stretchedHeightShellAllowance zeta alpha M)
      hn hnshell hncert.1 hH hncert.2
  have hlanding := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageOrbit p (stageCount h.omega M) n : ℝ) ≤
        Real.exp ((Real.log n) ^ (1 - delta))) hlandingM
  have hclock := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (stageClock p (stageCount h.omega M) n : ℝ) <
        (6953 / 1000 : ℝ) * Real.log n) hclockM
  have hraw := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ bootstrapSet p (stageCount h.omega M) →
      (rawTime n (stageClock p (stageCount h.omega M) n) : ℝ) <
        (261 / 25 : ℝ) * Real.log n) hrawM
  have hheight := eventuallyOfEventuallyShellwise
    (fun M n => n ∈ heightCertifiedShell p h.omega zeta alpha M →
      (∀ j : ℕ, j ≤ stageClock p (stageCount h.omega M) n →
        (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M / 2) ∧
      (∀ i : ℕ,
        i ≤ rawTime n (stageClock p (stageCount h.omega M) n) →
        (rawOrbit i n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha M)) hheightM
  refine ⟨S, hSdense, ?_⟩
  filter_upwards [hlanding, hclock, hraw, hheight,
    eventually_gt_atTop (0 : ℕ)] with n hlanding hclock hraw hheight hn hnS
  have hncert :
      n ∈ heightCertifiedShell p h.omega zeta alpha (Nat.log 2 n) := hnS
  have hnboot : n ∈ bootstrapSet p
      (stageCount h.omega (Nat.log 2 n)) := hncert.1
  let k := stageClock p (stageCount h.omega (Nat.log 2 n)) n
  let ell := rawTime n k
  have hallow := stretchedHeightShellAllowance_le_source
    hzeta.le halpha.le (mem_dyadicShell_log hn)
  have hheights := hheight hn hncert
  refine ⟨k, ell, hclock hn hnboot, hraw hn hnboot, ?_, ?_, ?_, ?_⟩
  · exact (rawOrbit_rawTime_eq_orbit n k).symm
  · rw [← stageOrbit_eq_orbit_stageClock]
    exact hlanding hn hnboot
  · intro j hj
    have hj' := hheights.1 j hj
    calc
      (orbit j n : ℝ) ≤
          (n : ℝ) * stretchedHeightShellAllowance zeta alpha
            (Nat.log 2 n) / 2 := hj'
      _ ≤ (n : ℝ) * stretchedHeightShellAllowance zeta alpha
          (Nat.log 2 n) := by
        have hn0 : 0 ≤ (n : ℝ) := by positivity
        have hH0 : 0 ≤ stretchedHeightShellAllowance zeta alpha
            (Nat.log 2 n) := by
          unfold stretchedHeightShellAllowance
          positivity
        nlinarith
      _ ≤ (n : ℝ) * Real.exp (zeta * (Real.log n) ^ (1 - delta)) := by
        dsimp [alpha] at hallow ⊢
        exact mul_le_mul_of_nonneg_left hallow (by positivity)
  · intro i hi
    have hi' := hheights.2 i hi
    exact hi'.trans (by
      dsimp [alpha] at hallow ⊢
      exact mul_le_mul_of_nonneg_left hallow (by positivity))
end FirstPassageLinearTransport
