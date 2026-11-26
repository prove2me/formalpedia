-- Prove2me | solution 1 for FirstPassageLinearTransport.ShrinkingRecertificationRun.toRankTrace
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:51:16.415091+00:00
-- url     : https://prove2.me/submissions/b6ca5003-6c8d-44ea-9911-c32c6370f947

import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierCore
import Definitions.Def_FirstPassageLinearTransport_TwoRegimeClock
import Definitions.Def_FirstPassageLinearTransport_ShrinkingBarrierRun
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighTolerance_lt_a0
import Theorems.Thm_FirstPassageLinearTransport_shrinkingHighSetup_M0
import Theorems.Thm_FirstPassageLinearTransport_ShrinkingRecertificationRun_certified_endpoint_shell_eq
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
import Theorems.Thm_FirstPassageLinearTransport_stageLength_le_shell
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
private theorem shrinking_rationalTargetRank_cast_le
    {r : ℚ} (hr : 0 ≤ r) (m : ℕ) :
    (rationalTargetRank r m : ℝ) ≤ (r : ℝ) * (m : ℝ) := by
  exact Nat.floor_le (mul_nonneg (by exact_mod_cast hr) (Nat.cast_nonneg m))
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
    (hrun : ShrinkingRecertificationRun P M S n elapsed q) :
    TwoRegimeRankTrace (P.rHi : ℝ) (P.rLo : ℝ) S M elapsed q := by
  have hrHi0 : (0 : ℚ) ≤ P.rHi := by exact_mod_cast P.pHi.r_pos.le
  have hrLo0 : (0 : ℚ) ≤ P.rLo := by exact_mod_cast P.pLo.r_pos.le
  induction hrun with
  | first hSM hM0 hnShell' hnGood =>
      exact TwoRegimeRankTrace.first
        (stageLength_le_shell (shrinkingHighSetup P M M) hM0 hnShell' hnGood)
        (shrinking_rationalTargetRank_cast_le hrHi0 M)
  | @nextHi elapsed qPrev m hrun hSm hm0 hsourceShell hsourceGood hgap ih =>
      have hmEq := hrun.certified_endpoint_shell_eq
        (shrinkingHighTolerance_lt_a0 P M m) hsourceGood hsourceShell
      have hmPrev : m ≤ qPrev := by omega
      apply TwoRegimeRankTrace.next ih hmPrev
        (stageLength_le_shell (shrinkingHighSetup P M m) hm0
          hsourceShell hsourceGood)
      simpa [hSm] using shrinking_rationalTargetRank_cast_le hrHi0 m
  | @nextLo elapsed qPrev m hrun hmS hm0 hsourceShell hsourceGood hgap ih =>
      have hmEq := hrun.certified_endpoint_shell_eq P.etaLo_lt_a0
        hsourceGood hsourceShell
      have hmPrev : m ≤ qPrev := by omega
      apply TwoRegimeRankTrace.next ih hmPrev
        (stageLength_le_shell P.pLo hm0 hsourceShell hsourceGood)
      simpa [show ¬ S ≤ m by omega] using
        shrinking_rationalTargetRank_cast_le hrLo0 m
end ShrinkingRecertificationRun
end FirstPassageLinearTransport
