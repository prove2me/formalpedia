-- Prove2me | solution 1 for FirstPassageLinearTransport.timeout_prefix_word_sum_lower
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:04:25.475798+00:00
-- url     : https://prove2.me/submissions/bd8da4d1-bf91-4769-808d-924cddd0ba60

import Definitions.Def_FirstPassageLinearTransport_TimeoutCore
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot
import Definitions.Def_FirstPassageLinearTransport_TimeoutDensity
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_boolParityWord
import Theorems.Thm_FirstPassageLinearTransport_orbit_scaled_lt_two_mul_parity
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
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_wordIncrementSum_collatz
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
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.stageClock_zero
attribute [local simp] FirstPassageLinearTransport.stageOrbit_zero
attribute [local simp] FirstPassageLinearTransport.stoppedBallotValue_cons



set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {K₀ : ℝ} {L m x : ℕ}
    (hx : x ∈ dyadicShell m)
    (htimeout : LowStageTimeout K₀ L m x)
    (hq : timeoutTargetRank K₀ L m ≤ m)
    (j : Fin (m + 1)) :
    -(((m + 2 - timeoutTargetRank K₀ L m : ℕ) : ℝ) * Real.log 2) <
      wordIncrementSum collatzLogIncrement (boolParityWord j x) := by
  let q := timeoutTargetRank K₀ L m
  let k := (j : ℕ)
  have hk : k ≤ m := by
    dsimp [k]
    omega
  have htimeoutj : 2 ^ q < orbit k x := by
    simpa [q, k] using htimeout j
  have hscaled := orbit_scaled_lt_two_mul_parity hx hk
  have hxupper : x < 2 ^ (m + 1) := (mem_dyadicShell.mp hx).2
  have hpowk : 0 < 2 ^ k := by positivity
  have hnat :
      2 ^ (q + k) < 3 ^ oddCount x k * 2 ^ (m + 2) := by
    calc
      2 ^ (q + k) = 2 ^ k * 2 ^ q := by
        rw [pow_add]
        ring
      _ < 2 ^ k * orbit k x :=
        Nat.mul_lt_mul_of_pos_left htimeoutj hpowk
      _ < 2 * 3 ^ oddCount x k * x := hscaled
      _ < 2 * 3 ^ oddCount x k * 2 ^ (m + 1) := by
        exact Nat.mul_lt_mul_of_pos_left hxupper (by positivity)
      _ = 3 ^ oddCount x k * 2 ^ (m + 2) := by
        rw [pow_succ]
        ring
  have hreal :
      (2 : ℝ) ^ (q + k) <
        (3 : ℝ) ^ oddCount x k * (2 : ℝ) ^ (m + 2) := by
    exact_mod_cast hnat
  have hlog := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < (2 : ℝ) ^ (q + k)))
    (Set.mem_Ioi.mpr
      (by positivity : (0 : ℝ) <
        (3 : ℝ) ^ oddCount x k * (2 : ℝ) ^ (m + 2))) hreal
  rw [Real.log_pow, Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlog
  have hqle : q ≤ m + 2 := hq.trans (by omega)
  have hcastsub : ((m + 2 - q : ℕ) : ℝ) =
      (m + 2 : ℝ) - (q : ℝ) := by
    rw [Nat.cast_sub hqle]
    push_cast
    rfl
  have hsum :
      wordIncrementSum collatzLogIncrement (boolParityWord j x) =
        (oddCount x k : ℝ) * Real.log 3 - (k : ℝ) * Real.log 2 := by
    rw [wordIncrementSum_collatz, card_boolSupport_boolParityWord]
  rw [hsum, hcastsub]
  push_cast at hlog ⊢
  linarith
end FirstPassageLinearTransport
