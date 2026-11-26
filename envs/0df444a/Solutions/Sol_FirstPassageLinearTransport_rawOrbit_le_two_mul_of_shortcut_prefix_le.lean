-- Prove2me | solution 1 for FirstPassageLinearTransport.rawOrbit_le_two_mul_of_shortcut_prefix_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T12:21:51.423112+00:00
-- url     : https://prove2.me/submissions/f49f38ba-18a8-4b68-aa07-88e104fc62be

import Definitions.Def_FirstPassageLinearTransport_NaturalDensityDescent
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Definitions.Def_FirstPassageLinearTransport_RawDynamics
import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
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
import Theorems.Thm_FirstPassageLinearTransport_oddCount_succ
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_succ
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawCollatz_eq_shortcut_of_even
import Theorems.Thm_FirstPassageLinearTransport_rawCollatz_of_odd
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_add
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_rawTime_eq_orbit
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_succ
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_two_eq_shortcut_of_odd
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_of_odd
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
    {n k : ℕ} {C : ℝ}
    (hshortcut : ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ C) :
    ∀ i : ℕ, i ≤ rawTime n k → (rawOrbit i n : ℝ) ≤ 2 * C := by
  induction k with
  | zero =>
      intro i hi
      have hi0 : i = 0 := by simpa [rawTime] using hi
      subst i
      have hnC := hshortcut 0 (by omega)
      simp [orbit_zero] at hnC
      have hC0 : 0 ≤ C := (Nat.cast_nonneg n).trans hnC
      simp only [rawOrbit_zero]
      linarith
  | succ k ih =>
      have hprev : ∀ j : ℕ, j ≤ k → (orbit j n : ℝ) ≤ C :=
        fun j hj => hshortcut j (hj.trans (Nat.le_succ k))
      have hIH := ih hprev
      intro i hi
      by_cases hiprev : i ≤ rawTime n k
      · exact hIH i hiprev
      · let q := i - rawTime n k
        have hiForm : i = q + rawTime n k := by
          dsimp [q]
          omega
        have hqPos : 0 < q := by dsimp [q]; omega
        have hrawBase : rawOrbit (rawTime n k) n = orbit k n :=
          rawOrbit_rawTime_eq_orbit n k
        rcases Nat.mod_two_eq_zero_or_one (orbit k n) with heven | hodd
        · have hbit : (parityBit n k : ℕ) = 0 := by
            simpa [parityBit] using heven
          have htimeSucc : rawTime n (k + 1) = rawTime n k + 1 := by
            simp [rawTime, oddCount_succ, hbit]
            omega
          have hq : q = 1 := by
            rw [htimeSucc] at hi
            dsimp [q]
            omega
          rw [hiForm, rawOrbit_add, hrawBase, hq, rawOrbit_succ,
            rawOrbit_zero, rawCollatz_eq_shortcut_of_even heven, ← orbit_succ]
          have hnext := hshortcut (k + 1) (by omega)
          have hC0 : 0 ≤ C := (Nat.cast_nonneg (orbit (k + 1) n)).trans hnext
          linarith
        · have hbit : (parityBit n k : ℕ) = 1 := by
            simpa [parityBit] using hodd
          have htimeSucc : rawTime n (k + 1) = rawTime n k + 2 := by
            simp [rawTime, oddCount_succ, hbit]
            omega
          have hqLe : q ≤ 2 := by
            rw [htimeSucc] at hi
            dsimp [q]
            omega
          have hnext := hshortcut (k + 1) (by omega)
          have hC0 : 0 ≤ C := (Nat.cast_nonneg (orbit (k + 1) n)).trans hnext
          have hqCases : q = 1 ∨ q = 2 := by omega
          rcases hqCases with hq | hq
          · rw [hiForm, hq, rawOrbit_add, hrawBase, rawOrbit_succ,
              rawOrbit_zero, rawCollatz_of_odd hodd]
            calc
              ((3 * orbit k n + 1 : ℕ) : ℝ) =
                  (2 : ℝ) * (orbit (k + 1) n : ℝ) := by
                exact_mod_cast (show 3 * orbit k n + 1 =
                  2 * orbit (k + 1) n by
                    rw [orbit_succ, shortcut_of_odd hodd]
                    omega)
              _ ≤ 2 * C :=
                mul_le_mul_of_nonneg_left hnext (by norm_num)
          · rw [hiForm, hq, rawOrbit_add, hrawBase,
              rawOrbit_two_eq_shortcut_of_odd hodd, ← orbit_succ]
            linarith
end FirstPassageLinearTransport
