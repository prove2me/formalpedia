-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_log_shellRankRpow_le_halfShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:35:16.881799+00:00
-- url     : https://prove2.me/submissions/54c26ae0-cea6-4c96-8a00-ffba4877ec1d

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFeasibleTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_shrinkingFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_reciprocalMaximumEpsilon_pos
import Theorems.Thm_FirstPassageLinearTransport_shortcutFirstPassageTime_self
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_cons
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_scale
attribute [local simp] FirstPassageLinearTransport.ballotWordValue_zero
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.bootstrapC_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapD_zero
attribute [local simp] FirstPassageLinearTransport.bootstrapSet_zero
attribute [local simp] FirstPassageLinearTransport.card_boolSupport_cons
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFeasibleTimes
attribute [local simp] FirstPassageLinearTransport.mem_shrinkingFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_timeoutFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_timeoutHighFirstBadSourcesAtRank
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcutFirstPassageTime_self
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0
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
    {q : ℝ} (hq : 0 ≤ q) :
    ∀ᶠ M : ℕ in atTop,
      Real.log (((M : ℝ) + 2) ^ q) ≤
        reciprocalMaximumEpsilon * ((M / 2 : ℕ) : ℝ) * Real.log 3 := by
  let d := reciprocalMaximumEpsilon * Real.log 3 / (4 * (q + 1))
  have hq1 : 0 < q + 1 := by linarith
  have hd : 0 < d := by
    dsimp [d]
    exact div_pos
      (mul_pos reciprocalMaximumEpsilon_pos
        (Real.log_pos (by norm_num)))
      (mul_pos (by norm_num) hq1)
  have hsmallReal := Real.isLittleO_log_id_atTop.bound hd
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (5 : ℕ)] with M hsmall hM
  let x : ℝ := (M : ℝ) + 2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hxPos : 0 < x := by dsimp [x]; positivity
  have hx1 : 1 ≤ x := by
    dsimp [x]
    have hM0 : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  change |Real.log x| ≤ d * |x| at hsmall
  rw [abs_of_nonneg hlog0, abs_of_nonneg hx0] at hsmall
  have hxHalfNat : M + 2 ≤ 4 * (M / 2) := by omega
  have hxHalf : x ≤ 4 * ((M / 2 : ℕ) : ℝ) := by
    dsimp [x]
    exact_mod_cast hxHalfNat
  have hqd : q * d ≤ reciprocalMaximumEpsilon * Real.log 3 / 4 := by
    dsimp [d]
    have hden : 0 < 4 * (q + 1) := by positivity
    have hfrac : q / (q + 1) ≤ 1 := by
      exact (div_le_one hq1).2 (by linarith)
    have hpos : 0 ≤ reciprocalMaximumEpsilon * Real.log 3 / 4 := by
      exact (div_nonneg
        (mul_nonneg reciprocalMaximumEpsilon_pos.le
          (Real.log_pos (by norm_num)).le) (by norm_num))
    calc
      q * (reciprocalMaximumEpsilon * Real.log 3 / (4 * (q + 1))) =
          (q / (q + 1)) *
            (reciprocalMaximumEpsilon * Real.log 3 / 4) := by
        field_simp [ne_of_gt hq1]
      _ ≤ 1 * (reciprocalMaximumEpsilon * Real.log 3 / 4) :=
        mul_le_mul_of_nonneg_right hfrac hpos
      _ = reciprocalMaximumEpsilon * Real.log 3 / 4 := one_mul _
  change Real.log (x ^ q) ≤ _
  rw [Real.log_rpow hxPos]
  calc
    q * Real.log x ≤ q * (d * x) :=
      mul_le_mul_of_nonneg_left hsmall hq
    _ = (q * d) * x := by ring
    _ ≤ (reciprocalMaximumEpsilon * Real.log 3 / 4) * x :=
      mul_le_mul_of_nonneg_right hqd hx0
    _ ≤ (reciprocalMaximumEpsilon * Real.log 3 / 4) *
        (4 * ((M / 2 : ℕ) : ℝ)) :=
      mul_le_mul_of_nonneg_left hxHalf (by
        exact div_nonneg
          (mul_nonneg reciprocalMaximumEpsilon_pos.le
            (Real.log_pos (by norm_num)).le) (by norm_num))
    _ = reciprocalMaximumEpsilon * ((M / 2 : ℕ) : ℝ) *
        Real.log 3 := by ring
end FirstPassageLinearTransport
