-- Prove2me | solution 1 for FirstPassageLinearTransport.eventually_timeoutRun_reverseProduct_half
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T13:15:08.759045+00:00
-- url     : https://prove2.me/submissions/c668419d-8455-4ed1-84bd-773c7a70bfeb

import Definitions.Def_FirstPassageLinearTransport_TimeoutOrbitCeiling
import Definitions.Def_FirstPassageLinearTransport_TimeoutRawClock
import Theorems.Thm_FirstPassageLinearTransport_CertifiedRankChain_scaledReverseLoss_le
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_currentRank_ge
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_scaledReverseLoss_le
import Theorems.Thm_FirstPassageLinearTransport_TimeoutRecertificationRun_source_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_eventually_rankTransport_small
import Theorems.Thm_FirstPassageLinearTransport_mem_dyadicShell
import Theorems.Thm_FirstPassageLinearTransport_one_sub_div_le_reverseProduct_of_scaledLoss
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingLowRatio
import Theorems.Thm_FirstPassageLinearTransport_tendsto_movingTerminalRank_atTop_of_sharp
import Theorems.Thm_FirstPassageLinearTransport_tendsto_shrinkingSwitchRank_atTop
attribute [local simp] FirstPassageLinearTransport.mem_dyadicShell



set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped Real Topology
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {Amax c beta : ℝ}
    (P : MovingEndpointParameterPackage Amax c beta)
    {A : ℕ → ℝ}
    (hbuffer : Tendsto (sharpMovingRankBuffer A) atTop atTop) :
    ∀ᶠ M : ℕ in atTop, ∀ {n elapsed q : ℕ},
      TimeoutRecertificationRun P.run.toTimeoutHigh P.K₀
        (movingTerminalRank A M) M (shrinkingSwitchRank P.Cswitch M)
        n elapsed q →
      (1 / 2 : ℚ) ≤ reverseProduct n elapsed := by
  have hTerminalT := tendsto_movingTerminalRank_atTop_of_sharp hbuffer
  have hSwitchT := tendsto_shrinkingSwitchRank_atTop P.Cswitch_pos
  have hSmallBase := eventually_rankTransport_small P.run.rStar_pos
  rw [eventually_atTop] at hSmallBase
  obtain ⟨Q, hQ⟩ := hSmallBase
  have hSwitchCast : Tendsto
      (fun M : ℕ => (shrinkingSwitchRank P.Cswitch M : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hSwitchT
  have hrHiR : (0 : ℝ) < (P.run.rHi : ℝ) := by
    exact_mod_cast P.run.pHi.r_pos
  have hHighT : Tendsto
      (fun M : ℕ => (P.run.rHi : ℝ) *
        (shrinkingSwitchRank P.Cswitch M : ℝ)) atTop atTop :=
    hSwitchCast.const_mul_atTop hrHiR
  have hHigh := (tendsto_atTop.1 hHighT) (Q : ℝ)
  have hQL := (tendsto_atTop.1 hTerminalT) (2 * Q)
  have hLowRatioBase : ∀ᶠ L : ℕ in atTop,
      (1 / 2 : ℝ) ≤ movingLowRatio P.K₀ L :=
    (tendsto_movingLowRatio P.K₀).eventually
      (Ici_mem_nhds (by norm_num : (1 / 2 : ℝ) < 1))
  have hLowRatio := hTerminalT.eventually hLowRatioBase
  have hStarHi : P.run.rStar ≤ P.run.rHi := by
    rw [P.run.rStar_eq]
    exact min_le_left _ _
  have hStarLoBase : ∀ᶠ L : ℕ in atTop,
      (P.run.rStar : ℝ) ≤ movingLowRatio P.K₀ L := by
    have hrStarOne : (P.run.rStar : ℝ) < 1 := by
      have hStarHiR : (P.run.rStar : ℝ) ≤ (P.run.rHi : ℝ) := by
        exact_mod_cast hStarHi
      exact hStarHiR.trans_lt P.run.pHi.r_lt_one
    exact (tendsto_movingLowRatio P.K₀).eventually
      (Ici_mem_nhds hrStarOne)
  have hStarLo := hTerminalT.eventually hStarLoBase
  filter_upwards [hHigh, hQL, hLowRatio, hStarLo] with M hHigh hQL
      hLowRatio hStarLo
  intro n elapsed q hrun
  have hqQ := hrun.currentRank_ge hHigh hLowRatio hQL
  have hsmall := hQ q hqQ
  have hnShell := hrun.source_mem_dyadicShell
  have hn : 0 < n := (by
    have hlo := (mem_dyadicShell.mp hnShell).1
    have hpow : 0 < 2 ^ M := by positivity
    omega)
  have hY : 0 < 2 ^ q := by positivity
  have hloss := hrun.scaledReverseLoss_le P.run.rStar_pos hStarHi hStarLo
  have hPlow := one_sub_div_le_reverseProduct_of_scaledLoss hn hY hloss
  have htwoThird : (2 / 3 : ℚ) ≤
      1 - ((((q + 2 : ℕ) : ℚ) / P.run.rStar) /
        ((2 ^ q : ℕ) : ℚ)) := by linarith
  exact (by norm_num : (1 / 2 : ℚ) ≤ 2 / 3).trans
    (htwoThird.trans hPlow)
end FirstPassageLinearTransport
