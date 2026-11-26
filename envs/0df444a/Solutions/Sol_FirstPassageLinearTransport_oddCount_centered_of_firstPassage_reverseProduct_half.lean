-- Prove2me | solution 1 for FirstPassageLinearTransport.oddCount_centered_of_firstPassage_reverseProduct_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:18:39.124751+00:00
-- url     : https://prove2.me/submissions/55f73a88-94bf-4c2d-8370-d631f6697f76

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_firstPassage_band
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
import Theorems.Thm_FirstPassageLinearTransport_orbit_pos
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_reverseProduct_le_one
import Theorems.Thm_FirstPassageLinearTransport_reverse_product_identity
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
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
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
    {n k M q : ℕ} {E : ℝ}
    (hn : 0 < n) (hnShell : n ∈ dyadicShell M)
    (hk : 0 < k) (hfp : IsFirstPassage (2 ^ q) n k)
    (hP : (1 / 2 : ℚ) ≤ reverseProduct n k)
    (hE : |driftGap * (k : ℝ) -
      (((M + 1 : ℕ) : ℝ) - (q : ℝ))| ≤ E) :
    |(oddCount n k : ℝ) - (k : ℝ) / 2| ≤
      (E + 2) * Real.log 2 / Real.log 3 := by
  let y := orbit k n
  have hy : 0 < y := orbit_pos hn k
  have hPposQ : (0 : ℚ) < reverseProduct n k :=
    (by norm_num : (0 : ℚ) < 1 / 2).trans_le hP
  have hPpos : (0 : ℝ) < (reverseProduct n k : ℝ) := by
    exact_mod_cast hPposQ
  have hPupQ := reverseProduct_le_one hn k
  have hPup : (reverseProduct n k : ℝ) ≤ 1 := by exact_mod_cast hPupQ
  have hidQ := reverse_product_identity hn k
  have hidR : (n : ℝ) =
      (((2 : ℝ) ^ k * (y : ℝ)) / (3 : ℝ) ^ oddCount n k) *
        (reverseProduct n k : ℝ) := by
    have hcast := congrArg (fun z : ℚ => (z : ℝ)) hidQ
    norm_num only [Rat.cast_natCast, Rat.cast_mul, Rat.cast_div,
      Rat.cast_pow] at hcast
    simpa [y] using hcast
  have hlogId := congrArg Real.log hidR
  rw [Real.log_mul (by positivity) hPpos.ne',
    Real.log_div (by positivity) (by positivity),
    Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow] at hlogId
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog3 : 0 < Real.log 3 := Real.log_pos (by norm_num)
  have hnBounds := mem_dyadicShell.mp hnShell
  have hnLoR : ((2 ^ M : ℕ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hnBounds.1
  have hnHiR : (n : ℝ) < ((2 ^ (M + 1) : ℕ) : ℝ) := by
    exact_mod_cast hnBounds.2
  have hlognLo := Real.log_le_log (by positivity) hnLoR
  have hlognHi := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by exact_mod_cast hn : (0 : ℝ) < n))
    (Set.mem_Ioi.mpr
      (by positivity : (0 : ℝ) < ((2 ^ (M + 1) : ℕ) : ℝ))) hnHiR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlognLo hlognHi
  simp only [Real.log_pow] at hlognLo hlognHi
  have hyUpperNat : y ≤ 2 ^ q := hfp.1
  have hyUpperR : (y : ℝ) ≤ ((2 ^ q : ℕ) : ℝ) := by
    exact_mod_cast hyUpperNat
  have hlogyUpper := Real.log_le_log (by positivity) hyUpperR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlogyUpper
  simp only [Real.log_pow] at hlogyUpper
  have hyLowerNat : 2 ^ q < 2 * y := (firstPassage_band hk hfp).1
  have hyLowerR : ((2 ^ q : ℕ) : ℝ) < 2 * (y : ℝ) := by
    exact_mod_cast hyLowerNat
  have hlogyLower := Real.strictMonoOn_log
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < ((2 ^ q : ℕ) : ℝ)))
    (Set.mem_Ioi.mpr (by positivity : (0 : ℝ) < 2 * (y : ℝ))) hyLowerR
  norm_num only [Nat.cast_pow, Nat.cast_ofNat] at hlogyLower
  rw [Real.log_pow,
    Real.log_mul (by norm_num)
      (Nat.cast_ne_zero.mpr (Nat.ne_of_gt hy))] at hlogyLower
  have hPcast : (((1 / 2 : ℚ) : ℝ)) ≤ (reverseProduct n k : ℝ) :=
    Rat.cast_le.2 hP
  norm_num at hPcast
  have hlogPLo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 2) hPcast
  have hlogPUp := Real.log_nonpos hPpos.le hPup
  rw [show (1 / 2 : ℝ) = 1 / 2 by norm_num,
    Real.log_div (by norm_num) (by norm_num), Real.log_one] at hlogPLo
  have hgaplog : driftGap * Real.log 2 = Real.log 2 - Real.log 3 / 2 := by
    unfold driftGap a0 logTwoThree
    field_simp [hlog2.ne']
  have hgapk :
      driftGap * (k : ℝ) * Real.log 2 =
        (k : ℝ) * Real.log 2 - (k : ℝ) / 2 * Real.log 3 := by
    calc
      driftGap * (k : ℝ) * Real.log 2 =
          (driftGap * Real.log 2) * (k : ℝ) := by ring
      _ = (Real.log 2 - Real.log 3 / 2) * (k : ℝ) := by rw [hgaplog]
      _ = (k : ℝ) * Real.log 2 - (k : ℝ) / 2 * Real.log 3 := by ring
  have hElo := (abs_le.mp hE).1
  have hEhi := (abs_le.mp hE).2
  push_cast at hElo hEhi hlognHi
  rw [abs_le]
  constructor
  · rw [← neg_div, div_le_iff₀ hlog3]
    nlinarith
  · rw [le_div_iff₀ hlog3]
    nlinarith
end FirstPassageLinearTransport
