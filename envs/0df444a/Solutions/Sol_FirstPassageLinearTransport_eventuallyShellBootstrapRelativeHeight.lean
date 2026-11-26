-- Prove2me | solution 1 for FirstPassageLinearTransport.eventuallyShellBootstrapRelativeHeight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:40:21.865036+00:00
-- url     : https://prove2.me/submissions/17794220-f8cb-487e-a928-a144ec0b3035

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_RawNaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_StretchedExceptionalCount
import Definitions.Def_FirstPassageLinearTransport_StretchedRelativeHeight
import Theorems.Thm_FirstPassageLinearTransport_stageMap_le_rpow_of_large
import Theorems.Thm_FirstPassageLinearTransport_orbit_le_root_of_stageClock_of_le_rpow
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_succ
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
import Theorems.Thm_FirstPassageLinearTransport_log_two_eq_of_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_initialWindowGood_of_mem_extended_of_large
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_add
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_le_two_mul_of_shortcut_prefix_le
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_succ
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageCount_gt_sub_one
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
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
    {r eta omega : ℝ} (p : StageSetup r eta)
    (homega : 0 < omega) (hre : r * (1 + eta) ≤ 1) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, ∀ H : ℝ,
      0 < n → n ∈ dyadicShell M →
      n ∈ bootstrapSet p (stageCount omega M) →
      4 ≤ H → n ∉ shellMultiplicativeHit M (H / 4) →
      (∀ j : ℕ, j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) * H / 2) ∧
      (∀ i : ℕ, i ≤ rawTime n (stageClock p (stageCount omega M) n) →
        (rawOrbit i n : ℝ) ≤ (n : ℝ) * H) := by
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 4) atTop atTop :=
    tendsto_atTop_add_const_right atTop 4 tendsto_natCast_atTop_atTop
  have hlogT : Tendsto (fun M : ℕ => Real.log ((M : ℝ) + 4)) atTop atTop :=
    Real.tendsto_log_atTop.comp hxT
  have hscaledT : Tendsto
      (fun M : ℕ => omega * Real.log ((M : ℝ) + 4)) atTop atTop :=
    Filter.Tendsto.const_mul_atTop homega hlogT
  have hstageLarge : ∀ᶠ M : ℕ in atTop,
      2 ≤ omega * Real.log ((M : ℝ) + 4) :=
    (tendsto_atTop.1 hscaledT) 2
  filter_upwards [eventually_ge_atTop p.M0, hstageLarge] with M hM hstageLarge
  intro n H hn hnshell hnboot hH hnHit
  have hstageCast := stageCount_gt_sub_one (omega := omega) M
  have hstagePos : 0 < stageCount omega M := by
    have hreal : (0 : ℝ) < stageCount omega M := by linarith
    exact_mod_cast hreal
  obtain ⟨R, hstageEq⟩ := Nat.exists_eq_succ_of_ne_zero hstagePos.ne'
  rw [hstageEq, bootstrapSet_succ] at hnboot
  have hnW : n ∈ extendedWindow p := hnboot.1
  have hchildSet : stageMap p n ∈ bootstrapSet p R := hnboot.2
  have hgood := mem_initialWindowGood_of_mem_extended_of_large p hnW (by
    simpa [log_two_eq_of_mem_dyadicShell hnshell] using hM)
  have hlen : stageLength p n ≤ M :=
    stageLength_le_shell p hM hnshell hgood
  have hmapPos : 0 < stageMap p n := by
    rw [stageMap_is_actual]
    exact orbit_pos hn _
  have hmap : (stageMap p n : ℝ) ≤ (n : ℝ) ^ r :=
    stageMap_le_rpow_of_large p hn hnW (by
      simpa [log_two_eq_of_mem_dyadicShell hnshell] using hM)
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hinitial :=
    initial_shortcut_raw_height_of_not_mem_shellMultiplicativeHit
      hnshell hnHit
  have hshortcut : ∀ j : ℕ,
      j ≤ stageClock p (stageCount omega M) n →
        (orbit j n : ℝ) ≤ (n : ℝ) * H / 2 := by
    intro j hj
    rw [hstageEq, stageClock_succ] at hj
    by_cases hjlen : j ≤ stageLength p n
    · exact (hinitial.1 j (hjlen.trans hlen)).le
    · let q := j - stageLength p n
      have hjform : j = stageLength p n + q := by
        dsimp [q]
        omega
      have hqclock : q ≤ stageClock p R (stageMap p n) := by
        dsimp [q]
        omega
      have htail := orbit_le_root_of_stageClock_of_le_rpow
        p hre hmapPos hchildSet hnOne hmap q hqclock
      rw [hjform, add_comm, orbit_add, ← stageMap_is_actual]
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      have hhalf : 1 ≤ H / 2 := by linarith
      exact htail.trans (by
        calc
          (n : ℝ) = (n : ℝ) * 1 := by ring
          _ ≤ (n : ℝ) * (H / 2) :=
            mul_le_mul_of_nonneg_left hhalf hn0
          _ = (n : ℝ) * H / 2 := by ring)
  refine ⟨hshortcut, ?_⟩
  intro i hi
  have hraw := rawOrbit_le_two_mul_of_shortcut_prefix_le hshortcut i hi
  calc
    (rawOrbit i n : ℝ) ≤ 2 * ((n : ℝ) * H / 2) := hraw
    _ = (n : ℝ) * H := by ring
end FirstPassageLinearTransport
