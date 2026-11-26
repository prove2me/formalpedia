-- Prove2me | solution 1 for FirstPassageLinearTransport.shellPrefixMultiplicativeHit_subset_shellTargetHeightFailure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:32.791195+00:00
-- url     : https://prove2.me/submissions/d5f57a5a-a2d0-4066-abb8-b67439dad40f

import Definitions.Def_FirstPassageLinearTransport_OrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Theorems.Thm_FirstPassageLinearTransport_exists_orbit_gt_mul_of_mem_shellPrefixMultiplicativeHit
import Theorems.Thm_FirstPassageLinearTransport_orbit_lower_by_halving
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
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {M h : ℕ} (hhM : h ≤ M) {u : ℝ} {f : ℕ → ℝ}
    (htarget : ∀ n : ℕ, n ∈ dyadicShell M →
      f n < (n : ℝ) / (2 : ℝ) ^ h) :
    shellPrefixMultiplicativeHit M h hhM u ⊆
      shellTargetHeightFailure M f u := by
  classical
  intro n hn
  simp only [shellTargetHeightFailure, Finset.mem_filter,
    Finset.mem_univ, true_and]
  intro hwitness
  obtain ⟨k, hkTarget, hkHeight⟩ := hwitness
  have hhk : h < k := by
    by_contra hnot
    have hkh : k ≤ h := Nat.le_of_not_gt hnot
    have hnPosNat : 0 < n.1 :=
      (pow_pos (by omega) M).trans_le (mem_dyadicShell.mp n.2).1
    have hnPos : 0 < (n.1 : ℝ) := by exact_mod_cast hnPosNat
    have hpow : (2 : ℝ) ^ k ≤ (2 : ℝ) ^ h :=
      pow_le_pow_right₀ (by norm_num) hkh
    have hdiv :
        (n.1 : ℝ) / (2 : ℝ) ^ h ≤
          (n.1 : ℝ) / (2 : ℝ) ^ k :=
      (div_le_div_iff_of_pos_left hnPos (by positivity) (by positivity)).2 hpow
    have hlower := orbit_lower_by_halving n.1 k
    linarith [htarget n.1 n.2]
  obtain ⟨j, hjh, hjHigh⟩ :=
    exists_orbit_gt_mul_of_mem_shellPrefixMultiplicativeHit hhM hn
  have hjk : j ≤ k := hjh.trans hhk.le
  exact (not_lt_of_ge (hkHeight j hjk)) hjHigh
end FirstPassageLinearTransport
