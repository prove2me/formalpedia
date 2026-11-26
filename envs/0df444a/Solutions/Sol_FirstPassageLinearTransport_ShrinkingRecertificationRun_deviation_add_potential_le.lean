-- Prove2me | solution 1 for FirstPassageLinearTransport.ShrinkingRecertificationRun.deviation_add_potential_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:05.507674+00:00
-- url     : https://prove2.me/submissions/df890b15-8976-4026-a07e-f3d68da9faec

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Definitions.Def_FirstPassageLinearTransport_ShrinkingTimeSupport
import Theorems.Thm_FirstPassageLinearTransport_certified_firstPassage_duration_error
import Theorems.Thm_FirstPassageLinearTransport_shrinkingTimePotential_step
import Theorems.Thm_FirstPassageLinearTransport_RecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_certified_endpoint_shell_eq
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_currentRank_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_M0_pos
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_mem_firstBadLandingEnvelope
import Theorems.Thm_FirstPassageLinearTransport_mem_generatedFirstBadSources
import Theorems.Thm_FirstPassageLinearTransport_mem_landingBad
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTaggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSources
import Theorems.Thm_FirstPassageLinearTransport_mem_lossFilteredTransportedSourcesAtTimes
import Theorems.Thm_FirstPassageLinearTransport_mem_prefixBad
import Theorems.Thm_FirstPassageLinearTransport_mem_taggedFiber
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_lt_a0
import Theorems.Thm_FirstPassageLinearTransport_stageLength_isFirstPassage
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
import Theorems.Thm_FirstPassageLinearTransport_stageLength_pos
import Theorems.Thm_FirstPassageLinearTransport_targetScale_rat
attribute [local simp] FirstPassageLinearTransport.StageSetup.lowerTolerance_M0
attribute [local simp] FirstPassageLinearTransport.boolParityCode_eq_word
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell
attribute [local simp] FirstPassageLinearTransport.mem_firstBadLandingEnvelope
attribute [local simp] FirstPassageLinearTransport.mem_generatedFirstBadSources
attribute [local simp] FirstPassageLinearTransport.mem_landingBad
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTaggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSources
attribute [local simp] FirstPassageLinearTransport.mem_lossFilteredTransportedSourcesAtTimes
attribute [local simp] FirstPassageLinearTransport.mem_prefixBad
attribute [local simp] FirstPassageLinearTransport.mem_taggedFiber
attribute [local simp] FirstPassageLinearTransport.mem_transportedSources
attribute [local simp] FirstPassageLinearTransport.oddCount_zero
attribute [local simp] FirstPassageLinearTransport.orbit_zero
attribute [local simp] FirstPassageLinearTransport.parityBit_zero
attribute [local simp] FirstPassageLinearTransport.rawOrbit_zero
attribute [local simp] FirstPassageLinearTransport.shortcut_zero
attribute [local simp] FirstPassageLinearTransport.shrinkingHighSetup_M0


section
namespace FirstPassageLinearTransport
open scoped Real
noncomputable section
private theorem abs_add_sub_one_le (a b : ℝ) :
    |a + b - 1| ≤ |a| + |b| + 1 := by
  calc
    |a + b - 1| ≤ |a + b| + 1 := by
      simpa using (abs_sub_le (a + b) 0 (1 : ℝ))
    _ ≤ |a| + |b| + 1 := by
      linarith [abs_add_le a b]
private theorem floor_rank_real_le
    {r : ℚ} (hr0 : 0 ≤ r) (m : ℕ) :
    (rationalTargetRank r m : ℝ) ≤ (r : ℝ) * (m : ℝ) := by
  exact Nat.floor_le (mul_nonneg (by exact_mod_cast hr0) (Nat.cast_nonneg m))
end
end FirstPassageLinearTransport
end

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped Real
noncomputable section
namespace FirstPassageLinearTransport
namespace ShrinkingRecertificationRun
theorem _root_.solution
    {P : ShrinkingBarrierRunData} {M S n elapsed q : ℕ}
    (hM : 1 ≤ M)
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    |driftGap * (elapsed : ℝ) - (((M + 1 : ℕ) : ℝ) - (q : ℝ))| +
        shrinkingTimePotential P M S q ≤
      shrinkingTimePotential P M S (M + 1) := by
  induction hrun with
  | first hSM hM0 hnShell hnGood =>
      have hlen := stageLength_le_shell (shrinkingHighSetup P M M)
        hM0 hnShell hnGood
      have hpos := stageLength_pos (shrinkingHighSetup P M M)
        hM0 hnShell hnGood
      have hfp : IsFirstPassage (2 ^ rationalTargetRank P.rHi M) n
          (stageLength (shrinkingHighSetup P M M) n) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (shrinkingHighSetup P M M)
            hM0 hnShell hnGood
      have herr := certified_firstPassage_duration_error
        (shrinkingHighTolerance_pos P M M).le
        (shrinkingHighTolerance_le_tau P M M |>.trans P.pHi.eta_le_one)
        hnShell hnGood hlen hpos hfp
      have hq := floor_rank_real_le
        (by exact_mod_cast P.pHi.r_pos.le : (0 : ℚ) ≤ P.rHi) M
      have hstep := shrinkingTimePotential_step P
        (S := S) (qPrev := M + 1) (m := M)
        (q := rationalTargetRank P.rHi M) hM hM rfl (by
        simpa [hSM] using hq)
      rw [if_pos hSM] at hstep
      have habs :
          |driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rHi M : ℝ))| ≤
            durationError (shrinkingHighTolerance P M M) M := by
        have hshift :
            driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
                (((M + 1 : ℕ) : ℝ) -
                  (rationalTargetRank P.rHi M : ℝ)) =
              (driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) - 1 := by
          push_cast
          ring
        rw [hshift]
        calc
          |(driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
              ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))) - 1| ≤
              |driftGap * (stageLength (shrinkingHighSetup P M M) n : ℝ) -
                ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ))| + 1 :=
            by
              simpa using (abs_sub_le
                (driftGap *
                  (stageLength (shrinkingHighSetup P M M) n : ℝ) -
                    ((M : ℝ) - (rationalTargetRank P.rHi M : ℝ)))
                0 (1 : ℝ))
          _ ≤ durationError (shrinkingHighTolerance P M M) M := by
            unfold durationError
            linarith
      linarith
  | @nextHi elapsed qPrev m hrun hSm hm0 hsourceShell hsourceGood hgap ih =>
      have hmEq := hrun.certified_endpoint_shell_eq
        (shrinkingHighTolerance_lt_a0 P M m) hsourceGood hsourceShell
      have hm1 : 1 ≤ m := P.pHi.M0_pos.trans hm0
      have hlen := stageLength_le_shell (shrinkingHighSetup P M m)
        hm0 hsourceShell hsourceGood
      have hpos := stageLength_pos (shrinkingHighSetup P M m)
        hm0 hsourceShell hsourceGood
      have hlocalfp : IsFirstPassage (2 ^ rationalTargetRank P.rHi m)
          (orbit elapsed n)
          (stageLength (shrinkingHighSetup P M m) (orbit elapsed n)) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage (shrinkingHighSetup P M m)
            hm0 hsourceShell hsourceGood
      have herr := certified_firstPassage_duration_error
        (shrinkingHighTolerance_pos P M m).le
        (shrinkingHighTolerance_le_tau P M m |>.trans P.pHi.eta_le_one)
        hsourceShell hsourceGood hlen hpos hlocalfp
      have hq := floor_rank_real_le
        (by exact_mod_cast P.pHi.r_pos.le : (0 : ℚ) ≤ P.rHi) m
      have hprevpos := hrun.currentRank_pos
      have hmPrevEq : qPrev = m + 1 := by omega
      have hstep := shrinkingTimePotential_step P
        (S := S) (qPrev := qPrev) (m := m)
        (q := rationalTargetRank P.rHi m) hM hm1 hmPrevEq (by
        simpa [hSm] using hq)
      rw [if_pos hSm] at hstep
      have hdecomp :
          driftGap * ((elapsed +
              stageLength (shrinkingHighSetup P M m) (orbit elapsed n) : ℕ) : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rHi m : ℝ)) =
            (driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap *
                (stageLength (shrinkingHighSetup P M m) (orbit elapsed n) : ℝ) -
              ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ))) - 1 := by
        rw [hmPrevEq]
        push_cast
        ring
      rw [hdecomp]
      have habs := abs_add_sub_one_le
        (driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)))
        (driftGap *
            (stageLength (shrinkingHighSetup P M m) (orbit elapsed n) : ℝ) -
          ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ)))
      have hlocal :
          |driftGap *
              (stageLength (shrinkingHighSetup P M m) (orbit elapsed n) : ℝ) -
            ((m : ℝ) - (rationalTargetRank P.rHi m : ℝ))| + 1 ≤
            durationError (shrinkingHighTolerance P M m) m := by
        unfold durationError
        linarith
      linarith
  | @nextLo elapsed qPrev m hrun hmS hm0 hsourceShell hsourceGood hgap ih =>
      have hmEq := hrun.certified_endpoint_shell_eq P.etaLo_lt_a0
        hsourceGood hsourceShell
      have hm1 : 1 ≤ m := P.pLo.M0_pos.trans hm0
      have hlen := stageLength_le_shell P.pLo hm0 hsourceShell hsourceGood
      have hpos := stageLength_pos P.pLo hm0 hsourceShell hsourceGood
      have hlocalfp : IsFirstPassage (2 ^ rationalTargetRank P.rLo m)
          (orbit elapsed n) (stageLength P.pLo (orbit elapsed n)) := by
        simpa [targetScale_rat] using
          stageLength_isFirstPassage P.pLo hm0 hsourceShell hsourceGood
      have herr := certified_firstPassage_duration_error P.pLo.eta_pos.le
        P.pLo.eta_le_one hsourceShell hsourceGood hlen hpos hlocalfp
      have hq := floor_rank_real_le
        (by exact_mod_cast P.pLo.r_pos.le : (0 : ℚ) ≤ P.rLo) m
      have hprevpos := hrun.currentRank_pos
      have hmPrevEq : qPrev = m + 1 := by omega
      have hstep := shrinkingTimePotential_step P
        (S := S) (qPrev := qPrev) (m := m)
        (q := rationalTargetRank P.rLo m) hM hm1 hmPrevEq (by
        simpa [show ¬ S ≤ m by omega] using hq)
      rw [if_neg (show ¬ S ≤ m by omega)] at hstep
      have hdecomp :
          driftGap * ((elapsed + stageLength P.pLo (orbit elapsed n) : ℕ) : ℝ) -
              (((M + 1 : ℕ) : ℝ) -
                (rationalTargetRank P.rLo m : ℝ)) =
            (driftGap * (elapsed : ℝ) -
              (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ))) +
            (driftGap * (stageLength P.pLo (orbit elapsed n) : ℝ) -
              ((m : ℝ) - (rationalTargetRank P.rLo m : ℝ))) - 1 := by
        rw [hmPrevEq]
        push_cast
        ring
      rw [hdecomp]
      have habs := abs_add_sub_one_le
        (driftGap * (elapsed : ℝ) -
          (((M + 1 : ℕ) : ℝ) - (qPrev : ℝ)))
        (driftGap * (stageLength P.pLo (orbit elapsed n) : ℝ) -
          ((m : ℝ) - (rationalTargetRank P.rLo m : ℝ)))
      have hlocal :
          |driftGap * (stageLength P.pLo (orbit elapsed n) : ℝ) -
            ((m : ℝ) - (rationalTargetRank P.rLo m : ℝ))| + 1 ≤
            durationError P.etaLo m := by
        unfold durationError
        linarith
      linarith
end ShrinkingRecertificationRun
end FirstPassageLinearTransport
