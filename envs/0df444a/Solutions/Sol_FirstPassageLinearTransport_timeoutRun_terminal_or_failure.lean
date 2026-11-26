-- Prove2me | solution 1 for FirstPassageLinearTransport.timeoutRun_terminal_or_failure
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:12:15.279048+00:00
-- url     : https://prove2.me/submissions/7d9cb5b5-ee43-4a74-b561-e9a1de21cc97

import Definitions.Def_FirstPassageLinearTransport_TimeoutEnvelope
import Definitions.Def_FirstPassageLinearTransport_TimeoutExecution
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_endpoint_mem_timeoutHighLandingBad
import Theorems.Thm_FirstPassageLinearTransport_StageSetup_lowerTolerance_M0
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_landingBand
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_source_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_cons
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_scale
import Theorems.Thm_FirstPassageLinearTransport_ballotWordValue_zero
import Theorems.Thm_FirstPassageLinearTransport_boolParityCode_eq_word
import Theorems.Thm_FirstPassageLinearTransport_bootstrapC_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapD_zero
import Theorems.Thm_FirstPassageLinearTransport_bootstrapSet_zero
import Theorems.Thm_FirstPassageLinearTransport_card_boolSupport_cons
import Theorems.Thm_FirstPassageLinearTransport_certified_landing_mem_lower_shell
import Theorems.Thm_FirstPassageLinearTransport_exists_lowTimeoutPassage_of_not_timeout
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
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_timeoutHighFirstBadSourcesAtRank
import Theorems.Thm_FirstPassageLinearTransport_mem_transportedSources
import Theorems.Thm_FirstPassageLinearTransport_oddCount_zero
import Theorems.Thm_FirstPassageLinearTransport_orbit_zero
import Theorems.Thm_FirstPassageLinearTransport_parityBit_zero
import Theorems.Thm_FirstPassageLinearTransport_rationalTargetRank_lt_parent
import Theorems.Thm_FirstPassageLinearTransport_rawOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_shortcut_zero
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_stageClock_zero
import Theorems.Thm_FirstPassageLinearTransport_stageOrbit_zero
import Theorems.Thm_FirstPassageLinearTransport_stoppedBallotValue_cons
import Theorems.Thm_FirstPassageLinearTransport_timeoutHighTolerance_lt_a0
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
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    (P : TimeoutHighRunData) (K₀ : ℝ)
    {L M S n elapsed q : ℕ}
    (hL2 : 2 ≤ L) (_hLS : L ≤ S)
    (hHiStartup : P.pHi.M0 ≤ L)
    (hnextPos : ∀ p ∈ Finset.Icc (L + 1) S,
      0 < timeoutTargetRank K₀ L (p - 1))
    (hnextParent : ∀ p ∈ Finset.Icc (L + 1) S,
      timeoutTargetRank K₀ L (p - 1) < p - 1)
    (hqM : q ≤ M - 1)
    (hrun : TimeoutRecertificationRun P K₀ L M S n elapsed q) :
    HasTimeoutTerminalLanding P K₀ L M S n ∨
      n ∈ timeoutSeparatedFailureEnvelope P K₀ M L S := by
  classical
  induction q using Nat.strong_induction_on generalizing elapsed with
  | h q ih =>
      by_cases hqL : q ≤ L
      · exact Or.inl (Or.inl ⟨elapsed, q, hqL, hrun⟩)
      · have hLq : L < q := Nat.lt_of_not_ge hqL
        let x := orbit elapsed n
        by_cases hqHigh : S < q
        · let t := timeoutHighTargetTolerance P M q
          by_cases hxGood : x ∈ initialWindowGood t
          · have hq1 : 1 ≤ q := by omega
            have hband := hrun.landingBand
            have hcert : x ∈ dyadicShell (q - 1) := by
              apply certified_landing_mem_lower_shell hq1
                (timeoutHighTolerance_lt_a0 P M (q - 1))
              · exact ⟨by
                  have hmul : 2 ^ (q - 1) * 2 < x * 2 := by
                    calc
                      2 ^ (q - 1) * 2 = 2 ^ q := by
                        calc
                          _ = 2 ^ ((q - 1) + 1) := (pow_succ _ _).symm
                          _ = 2 ^ q := by rw [Nat.sub_add_cancel hq1]
                      _ < 2 * x := hband.1
                      _ = x * 2 := by omega
                  exact lt_of_mul_lt_mul_right hmul (by norm_num), hband.2⟩
              · simpa [t, timeoutHighTargetTolerance] using hxGood
            have hmStartup : P.pHi.M0 ≤ q - 1 := by omega
            have hgap : rationalTargetRank P.rHi (q - 1) < q := by
              exact (rationalTargetRank_lt_parent
                (by exact_mod_cast P.pHi.r_pos.le)
                (by exact_mod_cast P.pHi.r_lt_one)
                (by omega)).trans (by omega)
            let nextRun : TimeoutRecertificationRun P K₀ L M S n
                (elapsed + stageLength (timeoutHighSetup P M (q - 1)) x)
                (rationalTargetRank P.rHi (q - 1)) :=
              TimeoutRecertificationRun.nextHi hrun (by omega) hmStartup
                (by omega) hcert (by
                  simpa [t, timeoutHighTargetTolerance] using hxGood) hgap
            exact ih _ hgap (hgap.le.trans hqM) nextRun
          · exact Or.inr (by
              unfold timeoutSeparatedFailureEnvelope
              apply Finset.mem_union_left
              apply Finset.mem_union_right
              apply Finset.mem_biUnion.mpr
              refine ⟨q, Finset.mem_Icc.mpr ⟨by omega, hqM⟩, ?_⟩
              exact mem_timeoutHighFirstBadSourcesAtRank.mpr
                ⟨hrun.source_mem_dyadicShell, elapsed, hrun,
                  hrun.endpoint_mem_timeoutHighLandingBad hxGood⟩)
        · have hqLow : q ≤ S := by omega
          by_cases hupper : x = 2 ^ q
          · exact Or.inl (Or.inr ⟨elapsed, q, hLq, hqLow, hrun, hupper⟩)
          · have hq1 : 1 ≤ q := by omega
            have hband := hrun.landingBand
            have hsourceShell : x ∈ dyadicShell (q - 1) := by
              rw [mem_dyadicShell]
              refine ⟨?_, ?_⟩
              · have hmul : 2 ^ (q - 1) * 2 < x * 2 := by
                  calc
                    2 ^ (q - 1) * 2 = 2 ^ q := by
                      calc
                        _ = 2 ^ ((q - 1) + 1) := (pow_succ _ _).symm
                        _ = 2 ^ q := by rw [Nat.sub_add_cancel hq1]
                    _ < 2 * x := hband.1
                    _ = x * 2 := by omega
                exact (lt_of_mul_lt_mul_right hmul (by norm_num)).le
              · have hxlt : x < 2 ^ q := lt_of_le_of_ne hband.2 hupper
                simpa [Nat.sub_add_cancel hq1] using hxlt
            have hpI : q ∈ Finset.Icc (L + 1) S :=
              Finset.mem_Icc.mpr ⟨by omega, hqLow⟩
            let m := q - 1
            by_cases htimeout : LowStageTimeout K₀ L m x
            · exact Or.inr (by
                unfold timeoutSeparatedFailureEnvelope
                apply Finset.mem_union_right
                apply Finset.mem_biUnion.mpr
                exact ⟨q, hpI,
                  mem_timeoutFirstBadSourcesAtRank.mpr
                    ⟨hrun.source_mem_dyadicShell, elapsed, hrun, by
                      simpa [m] using htimeout⟩⟩)
            · let hpass : LowTimeoutPassage K₀ L m x :=
                Classical.choice (exists_lowTimeoutPassage_of_not_timeout htimeout)
              have hqpos : 0 < timeoutTargetRank K₀ L m := by
                simpa [m] using hnextPos q hpI
              have hqparent : timeoutTargetRank K₀ L m < m := by
                simpa [m] using hnextParent q hpI
              have hgap : timeoutTargetRank K₀ L m < q :=
                hqparent.trans_le (by dsimp [m]; omega)
              have hmS : m < S := by dsimp [m]; omega
              have hLm : L ≤ m := by dsimp [m]; omega
              have hmPrevLo : m ≤ q := by dsimp [m]; omega
              have hmPrevHi : q ≤ m + 1 := by dsimp [m]; omega
              let nextRun : TimeoutRecertificationRun P K₀ L M S n
                  (elapsed + hpass.duration) (timeoutTargetRank K₀ L m) :=
                TimeoutRecertificationRun.nextLo hrun hmS hLm hmPrevLo
                  hmPrevHi hsourceShell hpass hqpos hqparent hgap
              exact ih _ hgap (hgap.le.trans hqM) nextRun
end FirstPassageLinearTransport
