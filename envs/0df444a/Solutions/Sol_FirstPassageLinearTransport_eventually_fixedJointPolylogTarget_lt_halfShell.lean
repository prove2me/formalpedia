-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_fixedJointPolylogTarget_lt_halfShell
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:36:35.003012+00:00
-- url     : https://prove2.me/submissions/41ea3a4e-5c7b-49ee-90cc-8404233e597a

import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
import Definitions.Def_FirstPassageLinearTransport_CriticalEndpointConsequences
import Definitions.Def_FirstPassageLinearTransport_FixedJointExceptionalOrder
import Theorems.Thm_FirstPassageLinearTransport_shell_log_le_rank_add_two
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
    {C A : ℝ} (hC : 0 < C) (hA : 0 ≤ A) :
    ∀ᶠ M : ℕ in atTop, ∀ n : ℕ, n ∈ dyadicShell M →
      fixedJointPolylogTarget C A n <
        (n : ℝ) / (2 : ℝ) ^ (M / 2) := by
  let b : ℝ := Real.log 2 / 8
  let d : ℝ := 1 / (C + 1)
  have hb : 0 < b := by
    dsimp [b]
    positivity
  have hd : 0 < d := by
    dsimp [d]
    positivity
  have hsmallReal :=
    (isLittleO_rpow_exp_pos_mul_atTop A hb).bound hd
  have hxT : Tendsto (fun M : ℕ => (M : ℝ) + 2) atTop atTop :=
    tendsto_atTop_add_const_right atTop 2 tendsto_natCast_atTop_atTop
  have hsmall := hxT.eventually hsmallReal
  filter_upwards [hsmall, eventually_ge_atTop (8 : ℕ)] with M hsmall hM
  intro n hn
  let x : ℝ := (M : ℝ) + 2
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hlogn0 : 0 ≤ Real.log n := by
    apply Real.log_nonneg
    have hnLower := (mem_dyadicShell.mp hn).1
    have hpow : 1 ≤ 2 ^ M := one_le_pow₀ (by norm_num)
    exact_mod_cast hpow.trans hnLower
  have hlogUpper : Real.log n ≤ x := by
    simpa [x] using shell_log_le_rank_add_two hn
  have hpowUpper : (Real.log n) ^ A ≤ x ^ A :=
    Real.rpow_le_rpow hlogn0 hlogUpper hA
  have hsmall' : x ^ A ≤ d * Real.exp (b * x) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hx0 A)] at hsmall
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] at hsmall
    simpa [x] using hsmall
  have hCd : C * d < 1 := by
    dsimp [d]
    have hC1 : 0 < C + 1 := by linarith
    rw [mul_one_div]
    exact (div_lt_one hC1).2 (by linarith)
  have htargetExp : fixedJointPolylogTarget C A n <
      Real.exp (b * x) := by
    unfold fixedJointPolylogTarget
    calc
      C * (Real.log n) ^ A ≤ C * (x ^ A) :=
        mul_le_mul_of_nonneg_left hpowUpper hC.le
      _ ≤ C * (d * Real.exp (b * x)) :=
        mul_le_mul_of_nonneg_left hsmall' hC.le
      _ < 1 * Real.exp (b * x) := by
        have hexp := Real.exp_pos (b * x)
        nlinarith
      _ = Real.exp (b * x) := one_mul _
  let h := M / 2
  have hhM : h ≤ M := by dsimp [h]; omega
  have hbx : b * x ≤ ((M - h : ℕ) : ℝ) * Real.log 2 := by
    dsimp [b, x, h]
    have hlog2 := (Real.log_pos (by norm_num : (1 : ℝ) < 2)).le
    have hMx : (M : ℝ) + 2 ≤ 2 * (M : ℝ) := by
      exact_mod_cast (by omega : M + 2 ≤ 2 * M)
    have hquarter : ((M : ℝ) + 2) / 8 ≤ (M : ℝ) / 4 := by linarith
    have htwiceNat : M ≤ 2 * (M - M / 2) := by omega
    have htwice : (M : ℝ) ≤ 2 * ((M - M / 2 : ℕ) : ℝ) := by
      exact_mod_cast htwiceNat
    have hgap : (M : ℝ) / 4 ≤ ((M - M / 2 : ℕ) : ℝ) := by
      linarith
    nlinarith
  have hexpPow : Real.exp (b * x) ≤ (2 : ℝ) ^ (M - h) := by
    calc
      Real.exp (b * x) ≤
          Real.exp (((M - h : ℕ) : ℝ) * Real.log 2) :=
        Real.exp_le_exp.mpr hbx
      _ = (2 : ℝ) ^ (M - h) := by
        rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hnLower : (2 : ℝ) ^ M ≤ (n : ℝ) := by
    exact_mod_cast (mem_dyadicShell.mp hn).1
  have hpowhPos : 0 < (2 : ℝ) ^ h := by positivity
  have hhalving : (2 : ℝ) ^ (M - h) ≤
      (n : ℝ) / (2 : ℝ) ^ h := by
    apply (le_div_iff₀ hpowhPos).2
    rw [← pow_add]
    have hadd : M - h + h = M := Nat.sub_add_cancel hhM
    simpa [hadd] using hnLower
  exact htargetExp.trans_le (hexpPow.trans hhalving)
end FirstPassageLinearTransport
