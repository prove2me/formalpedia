-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_lt_two_mul_of_not_mem_shellMultiplicativeHit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:17:45.315117+00:00
-- url     : https://prove2.me/submissions/550a6a4b-19f8-4682-8a2c-edf2e554dcd7

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Theorems.Thm_FirstPassageLinearTransport_multiplicative_prefix_le_of_not_crosses
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
import Theorems.Thm_FirstPassageLinearTransport_orbit_scaled_lt_two_mul_parity
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
    {M n : ℕ} {u : ℝ}
    (hn : n ∈ dyadicShell M) (hnGood : n ∉ shellMultiplicativeHit M u)
    {j : ℕ} (hj : j ≤ M) :
    (orbit j n : ℝ) < 2 * u * n := by
  have hsafe :
      ¬crossesMultiplicativeFrom u M 1 (boolParityWord M n) := by
    simpa [shellMultiplicativeHit, hn] using hnGood
  have hmult := multiplicative_prefix_le_of_not_crosses
    (z := 1) (by norm_num) hsafe j hj
  have hscaled := orbit_scaled_lt_two_mul_parity hn hj
  have hpow : 0 < (2 : ℝ) ^ j := by positivity
  have hscaledR :
      (2 : ℝ) ^ j * (orbit j n : ℝ) <
        2 * (3 : ℝ) ^ oddCount n j * (n : ℝ) := by
    exact_mod_cast hscaled
  have hFn :
      ((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) * (n : ℝ) ≤
        u * (n : ℝ) := by
    have hF : (3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j ≤ u := by
      simpa using hmult
    gcongr
  apply lt_of_mul_lt_mul_left (a := (2 : ℝ) ^ j) _ hpow.le
  calc
    (2 : ℝ) ^ j * (orbit j n : ℝ) <
        2 * (3 : ℝ) ^ oddCount n j * (n : ℝ) := hscaledR
    _ = (2 : ℝ) ^ j *
        (2 * (((3 : ℝ) ^ oddCount n j / (2 : ℝ) ^ j) *
          (n : ℝ))) := by field_simp
    _ ≤ (2 : ℝ) ^ j * (2 * (u * (n : ℝ))) := by gcongr
    _ = (2 : ℝ) ^ j * (2 * u * n) := by ring
end FirstPassageLinearTransport
