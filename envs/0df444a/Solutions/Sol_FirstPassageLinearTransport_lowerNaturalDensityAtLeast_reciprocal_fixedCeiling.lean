-- Prove2me | solution 1 for FirstPassageLinearTransport.lowerNaturalDensityAtLeast_reciprocal_fixedCeiling
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:43:23.355896+00:00
-- url     : https://prove2.me/submissions/57048f38-4adb-44c7-b678-dc78082edf08

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_lowerNaturalDensityAtLeast_targetHeightFailure_fixedPrefix
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
import Theorems.Thm_FirstPassageLinearTransport_reciprocalMaximumEpsilon_pos
import Theorems.Thm_FirstPassageLinearTransport_reciprocal_finite_multiplicative_maximum
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
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {u : ℝ} (hu : 1 ≤ u) {f : ℕ → ℝ}
    (hsublinear : ∀ h : ℕ,
      ∀ᶠ n : ℕ in Filter.atTop,
        f n < (n : ℝ) / (2 : ℝ) ^ h) :
    LowerNaturalDensityAtLeast (targetHeightFailureSet f u) (2 / (3 * u)) := by
  intro d hd
  have huPos : 0 < u := zero_lt_one.trans_le hu
  have hDPos : 0 < 2 / (3 * u) := by positivity
  have hgap : 0 < 2 / (3 * u) - d := by linarith
  have hepsLogPos :
      0 < reciprocalMaximumEpsilon * Real.log 3 :=
    mul_pos reciprocalMaximumEpsilon_pos (Real.log_pos (by norm_num))
  let threshold : ℝ := max 1 <|
    max (Real.log u /
      (reciprocalMaximumEpsilon * Real.log 3))
      ((2 / (3 * u)) * reciprocalMaximumConstant /
        (2 / (3 * u) - d))
  obtain ⟨h : ℕ, hh⟩ := exists_nat_gt threshold
  have hhOneR : (1 : ℝ) < h :=
    (le_max_left _ _).trans_lt hh
  have hhPos : 0 < h := by
    exact_mod_cast (show (0 : ℝ) < h by linarith)
  have hhSlope :
      Real.log u /
          (reciprocalMaximumEpsilon * Real.log 3) < (h : ℝ) :=
    ((le_max_left _ _).trans (le_max_right (1 : ℝ) _)).trans_lt hh
  have hlog :
      Real.log u ≤
        reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3 := by
    have hmul := (div_lt_iff₀ hepsLogPos).1 hhSlope
    nlinarith
  have hhLoss :
      (2 / (3 * u)) * reciprocalMaximumConstant /
          (2 / (3 * u) - d) < (h : ℝ) :=
    ((le_max_right _ _).trans (le_max_right (1 : ℝ) _)).trans_lt hh
  have hlossMul := (div_lt_iff₀ hgap).1 hhLoss
  have hhRPos : 0 < (h : ℝ) := by exact_mod_cast hhPos
  have hlowerD :
      d < (2 / (3 * u)) *
        (1 - reciprocalMaximumConstant / (h : ℝ)) := by
    have hloss :
        (2 / (3 * u)) * reciprocalMaximumConstant / (h : ℝ) <
          2 / (3 * u) - d := by
      apply (div_lt_iff₀ hhRPos).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using hlossMul
    calc
      d < 2 / (3 * u) -
          (2 / (3 * u)) * reciprocalMaximumConstant / (h : ℝ) := by
        linarith
      _ = (2 / (3 * u)) *
          (1 - reciprocalMaximumConstant / (h : ℝ)) := by ring
  have hfinite := reciprocal_finite_multiplicative_maximum hu hhPos hlog
  have hdHit :
      d < (multiplicativeHitCount u h 1 : ℝ) / (2 : ℝ) ^ h :=
    hlowerD.trans_le hfinite.1
  exact lowerNaturalDensityAtLeast_targetHeightFailure_fixedPrefix
    (hsublinear h) d hdHit
end FirstPassageLinearTransport
