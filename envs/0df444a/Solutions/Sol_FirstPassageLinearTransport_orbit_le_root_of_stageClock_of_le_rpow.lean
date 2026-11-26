-- Prove2me | solution 1 for FirstPassageLinearTransport.orbit_le_root_of_stageClock_of_le_rpow
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:39:09.899049+00:00
-- url     : https://prove2.me/submissions/cae89fe9-46eb-4754-92f0-2a357d624092

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_stageMap_le_self
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_add
import Theorems.Thm_FirstPassageLinearTransport_orbit_le_one_add_eta_of_le_stageLength
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_succ
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageMap_is_actual
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
    {r eta : ℝ} (p : StageSetup r eta)
    (hre : r * (1 + eta) ≤ 1)
    {R m : ℕ} {root : ℝ}
    (hm : 0 < m) (hmSet : m ∈ bootstrapSet p R)
    (hroot : 1 ≤ root) (hmroot : (m : ℝ) ≤ root ^ r) :
    ∀ j : ℕ, j ≤ stageClock p R m → (orbit j m : ℝ) ≤ root := by
  induction R generalizing m with
  | zero =>
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      subst j
      rw [orbit_zero]
      calc
        (m : ℝ) ≤ root ^ r := hmroot
        _ ≤ root ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hroot p.r_lt_one.le
        _ = root := Real.rpow_one root
  | succ R ih =>
      rw [bootstrapSet_succ] at hmSet
      have hmW : m ∈ extendedWindow p := hmSet.1
      have hchildSet : stageMap p m ∈ bootstrapSet p R := hmSet.2
      have hchildPos : 0 < stageMap p m := by
        rw [stageMap_is_actual]
        exact orbit_pos hm _
      have hmapLe : (stageMap p m : ℝ) ≤ root ^ r := by
        have hcast : (stageMap p m : ℝ) ≤ (m : ℝ) := by
          exact_mod_cast stageMap_le_self p hm hmW
        exact hcast.trans hmroot
      intro j hj
      by_cases hjlen : j ≤ stageLength p m
      · have hlocal := orbit_le_one_add_eta_of_le_stageLength p hm hmW hjlen
        have hm0 : 0 ≤ (m : ℝ) := by positivity
        have hraise : (m : ℝ) ^ (1 + eta) ≤
            (root ^ r) ^ (1 + eta) :=
          Real.rpow_le_rpow hm0 hmroot (by linarith [p.eta_pos])
        have hroot0 : 0 < root := zero_lt_one.trans_le hroot
        calc
          (orbit j m : ℝ) ≤ (m : ℝ) ^ (1 + eta) := hlocal
          _ ≤ (root ^ r) ^ (1 + eta) := hraise
          _ = root ^ (r * (1 + eta)) := by
            rw [Real.rpow_mul hroot0.le]
          _ ≤ root ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le hroot hre
          _ = root := Real.rpow_one root
      · let q := j - stageLength p m
        have hjform : j = stageLength p m + q := by
          dsimp [q]
          omega
        have hqclock : q ≤ stageClock p R (stageMap p m) := by
          rw [stageClock_succ] at hj
          dsimp [q]
          omega
        rw [hjform, add_comm, orbit_add, ← stageMap_is_actual]
        exact ih hchildPos hchildSet hmapLe q hqclock
end FirstPassageLinearTransport
