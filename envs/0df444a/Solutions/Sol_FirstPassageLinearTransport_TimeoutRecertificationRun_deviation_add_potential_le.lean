-- Prove2me | solution 1 for FirstPassageLinearTransport.TimeoutRecertificationRun.deviation_add_potential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:14:10.038433+00:00
-- url     : https://prove2.me/submissions/e14a4d85-9fcd-44bc-874e-4cb9e9284b04

import Definitions.Def_FirstPassageLinearTransport_TimeoutRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingSchedules
import Definitions.Def_FirstPassageLinearTransport_TimeoutTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_timeoutCertified_duration_error
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_high_step
import Theorems.Thm_FirstPassageLinearTransport_timeoutTimePotential_low_step
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_M0_pos
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
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageLength_isFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
import Theorems.Thm_FirstPassageLinearTransport_stageLength_pos
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_targetScale_rat
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
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
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


section
namespace FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
private theorem timeout_abs_add_sub_one_le (a b : ℝ) :
    |a + b - 1| ≤ |a| + |b| + 1 := by
  calc
    |a + b - 1| ≤ |a + b| + 1 := by
      simpa using (abs_sub_le (a + b) 0 (1 : ℝ))
    _ ≤ |a| + |b| + 1 := by
      linarith [abs_add_le a b]
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
namespace TimeoutRecertificationRun
theorem _root_.solution
    {P : TimeoutHighRunData} {K₀ : ℝ}
    {L M S n elapsed q : ℕ} (hM : 1 ≤ M)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| +
        timeoutTimePotential P M S q ≤
      timeoutTimePotential P M S (M + 1) := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      have hlen := stageLength_le_shell (timeoutHighSetup P M M)
        hM0 hnShell hnGood
      have hpos := stageLength_pos (timeoutHighSetup P M M)
        hM0 hnShell hnGood
      have hfp : IsFirstPassage (2 ^ rationalTargetRank P.rHi M) n
          (stageLength (timeoutHighSetup P M M) n) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (timeoutHighSetup P M M)
            hM0 hnShell hnGood
      have herr := timeoutCertified_duration_error
        (timeoutHighTolerance_pos P M M).le
        ((timeoutHighTolerance_le_tau P M M).trans P.pHi.eta_le_one)
        hnShell hnGood hlen hpos hfp
      have hq : (rationalTargetRank P.rHi M : ℝ) ≤
          (P.rHi : ℝ) * (M : ℝ) := by
        have hnonneg : 0 ≤ (P.rHi : ℝ) * (M : ℝ) :=
          mul_nonneg P.pHi.r_pos.le (Nat.cast_nonneg M)
        exact Nat.floor_le hnonneg
      have hstep := timeoutTimePotential_high_step P
        (S := S) (m := M) (q := rationalTargetRank P.rHi M)
        hM hM hSM hq
      have habs :
          |driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rHi M : ℝ))| ≤
            timeoutDurationError (timeoutHighTolerance P M M) M := by
        have hshift :
            driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
                (((M + 1 : ℕ) : ℝ) -
                  (rationalTargetRank P.rHi M : ℝ)) =
              (driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) - 1 := by
          push_cast
          ring
        rw [hshift]
        calc
          |(driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
              ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) - 1| ≤
              |driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))| + 1 := by
            simpa using (abs_sub_le
              (driftGap * (stageLength (timeoutHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) 0 (1 : ℝ))
          _ ≤ timeoutDurationError (timeoutHighTolerance P M M) M := by
            unfold timeoutDurationError
            linarith
      linarith
  | @nextHi elapsed qPrev m hrun hSm hm0 hmPrev hsourceShell hsourceGood hgap ih =>
      have hm1 : 1 ≤ m := P.pHi.M0_pos.trans hm0
      have hlen := stageLength_le_shell (timeoutHighSetup P M m)
        hm0 hsourceShell hsourceGood
      have hpos := stageLength_pos (timeoutHighSetup P M m)
        hm0 hsourceShell hsourceGood
      have hlocalfp : IsFirstPassage (2 ^ rationalTargetRank P.rHi m)
          (orbit elapsed n)
          (stageLength (timeoutHighSetup P M m) (orbit elapsed n)) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (timeoutHighSetup P M m)
            hm0 hsourceShell hsourceGood
      have herr := timeoutCertified_duration_error
        (timeoutHighTolerance_pos P M m).le
        ((timeoutHighTolerance_le_tau P M m).trans P.pHi.eta_le_one)
        hsourceShell hsourceGood hlen hpos hlocalfp
      have hq : (rationalTargetRank P.rHi m : ℝ) ≤
          (P.rHi : ℝ) * (m : ℝ) := by
        have hnonneg : 0 ≤ (P.rHi : ℝ) * (m : ℝ) :=
          mul_nonneg P.pHi.r_pos.le (Nat.cast_nonneg m)
        exact Nat.floor_le hnonneg
      have hstep := timeoutTimePotential_high_step P
        (S := S) (m := m) (q := rationalTargetRank P.rHi m)
        hM hm1 hSm hq
      rw [←hmPrev] at hstep
      have hdecomp :
          driftGap * ((elapsed +
              stageLength (timeoutHighSetup P M m) (orbit elapsed n) : ℕ) : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rHi m : ℝ)) =
            (driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap *
                (stageLength (timeoutHighSetup P M m) (orbit elapsed n) : ℝ) -
              ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ))) - 1 := by
        rw [hmPrev]
        push_cast
        ring
      rw [hdecomp]
      have habs := timeout_abs_add_sub_one_le
        (driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)))
        (driftGap *
            (stageLength (timeoutHighSetup P M m) (orbit elapsed n) : ℝ) -
          ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ)))
      have hlocal :
          |driftGap *
              (stageLength (timeoutHighSetup P M m) (orbit elapsed n) : ℝ) -
            ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ))| + 1 ≤
            timeoutDurationError (timeoutHighTolerance P M m) m := by
        unfold timeoutDurationError
        linarith
      linarith
  | @nextLo elapsed qPrev m hrun hmS hLm hmPrevLo hmPrevHi hsourceShell hpass
      hqpos hqparent hgap ih =>
      have hstep := timeoutTimePotential_low_step P (M := M) hmS hpass
        hmPrevLo hmPrevHi hqparent
      let e : ℕ := qPrev - m
      have heLe : e ≤ 1 := by
        dsimp [e]
        omega
      have heEq : (e : ℝ) = (qPrev : ℝ) - (m : ℝ) := by
        dsimp [e]
        rw [Nat.cast_sub hmPrevLo]
      have hdecomp :
          driftGap * ((elapsed + hpass.duration : ℕ) : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (timeoutTargetRank K₀ L m : ℝ)) =
            (driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ) := by
        rw [heEq]
        push_cast
        ring
      rw [hdecomp]
      have he0 : (0 : ℝ) ≤ e := Nat.cast_nonneg e
      have he1 : (e : ℝ) ≤ 1 := by exact_mod_cast heLe
      have habs0 := abs_sub_le
        ((driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
        (driftGap * (hpass.duration : ℝ) -
          ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ)))) 0 (e : ℝ)
      have habsAdd := abs_add_le
        (driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)))
        (driftGap * (hpass.duration : ℝ) -
          ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ)))
      have habs :
          |(driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ)| ≤
            |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
            |driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1 := by
        have heabs : |(e : ℝ)| ≤ 1 := by rw [abs_of_nonneg he0]; exact he1
        have habsSub :
            |(driftGap * (elapsed : ℝ) -
                (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
              (driftGap * (hpass.duration : ℝ) -
                ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ)| ≤
              |(driftGap * (elapsed : ℝ) -
                  (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
                (driftGap * (hpass.duration : ℝ) -
                  ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ)))| + |(e : ℝ)| := by
          simpa using habs0
        calc
          |(driftGap * (elapsed : ℝ) -
                (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
              (driftGap * (hpass.duration : ℝ) -
                ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ)| ≤
            |(driftGap * (elapsed : ℝ) -
                  (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
                (driftGap * (hpass.duration : ℝ) -
                  ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ)))| + |(e : ℝ)| :=
              habsSub
          _ ≤ (|driftGap * (elapsed : ℝ) -
                (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
              |driftGap * (hpass.duration : ℝ) -
                ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))|) +
              |(e : ℝ)| := by gcongr
          _ ≤ _ := by linarith
      calc
        |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)) +
            (driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))) - (e : ℝ)| +
            timeoutTimePotential P M S (timeoutTargetRank K₀ L m) ≤
          (|driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
            |driftGap * (hpass.duration : ℝ) -
              ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
            timeoutTimePotential P M S (timeoutTargetRank K₀ L m) :=
              add_le_add habs (le_refl _)
        _ = |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
            ((|driftGap * (hpass.duration : ℝ) -
                ((m : ℝ) - (timeoutTargetRank K₀ L m : ℝ))| + 1) +
              timeoutTimePotential P M S (timeoutTargetRank K₀ L m)) := by ring
        _ ≤ |driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))| +
            timeoutTimePotential P M S qPrev :=
              add_le_add (le_refl _) hstep
        _ ≤ timeoutTimePotential P M S (M + 1) := ih
end TimeoutRecertificationRun
end FirstPassageLinearTransport
