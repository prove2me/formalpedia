-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.DeficitSplitLemmas.high_bucket_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:26.965263+00:00
-- url     : https://prove2.me/submissions/025ba9d3-745c-40c0-b138-fabbaefed3b3

import Definitions.Def_Formalism_SizeWindowBrackets_SecondKindBucket
import Definitions.Def_Formalism_LogFactorialBounds_LogFactorialProofs_PrimeSum
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_RankGapDecayHypothesis
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_PmModulusFacts
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FourNotDvdOddSqAddOne
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AdmissibleSchurLemma
import Theorems.Thm_Formalism_LFunctionChainParameters_DeficitSplitLemmas_interval_count

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.DeficitSplitLemmas
open Finset Classical
noncomputable section
namespace Formalism.LFunctionChainParameters.DeficitSplitLemmas
theorem _root_.solution : HighBucket := by
  intro a at_ w'' X'' th s I w hw'' hth0 hth1 hX ha hat0 hat hs hI hw
  simp only [askAt]
  have hX0 : 0 < X'' := by linarith
  have hl2X : 0 ≤ Real.log (2 * X'') := Real.log_nonneg (by linarith)

  have hper : ∀ p ∈ s, 2 * Real.log p * ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤
      (if (p : ℝ) < X'' * (1 + th) then 2 * Real.log (2 * X'') * (w'' * th) else 0) := by
    intro p hp
    have hpX : X'' < p := hs p hp
    have hp0 : (0 : ℝ) < p := by linarith
    have hlp : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    set bp : ℝ := if (p : ℝ) < X'' * (1 + th) then w'' * th else 0 with hbp
    have hbp0 : 0 ≤ bp := by
      rw [hbp]; split_ifs
      · positivity
      · exact le_rfl
    have hi : ∀ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ if i = 1 then bp else 0 := by
      intro i hiI
      have hi1 := hI p hp i hiI
      by_cases h1 : i = 1
      · subst h1
        rw [if_pos rfl, pow_one]
        apply max_le _ hbp0
        rw [hbp]
        split_ifs with hlt
        · have h2 : at_ / (p : ℝ) ≤ at_ / X'' := div_le_div_of_nonneg_left hat0 hX0 hpX.le
          have h3 : at_ / X'' ≤ w'' * (1 + th) := by
            rw [div_le_iff₀ hX0]; rw [← ha] at hat; nlinarith
          linarith [hw p hp 1 hiI]
        · have hge : X'' * (1 + th) ≤ p := not_lt.1 hlt
          have h2 : at_ / (p : ℝ) ≤ w'' := by
            rw [div_le_iff₀ hp0]; rw [← ha] at hat
            nlinarith
          linarith [hw p hp 1 hiI]
      · rw [if_neg h1]
        apply max_le _ le_rfl
        have hi2 : 2 ≤ i := by omega
        have hpow : (p : ℝ) ^ 2 ≤ (p : ℝ) ^ i := pow_le_pow_right₀ (by linarith) hi2
        have hp2 : 2 * X'' ≤ (p : ℝ) ^ 2 := by nlinarith
        have hpi0 : (0 : ℝ) < (p : ℝ) ^ i := by positivity
        have h2 : at_ / (p : ℝ) ^ i ≤ w'' := by
          rw [div_le_iff₀ hpi0]; rw [← ha] at hat
          have : at_ ≤ w'' * (2 * X'') := by nlinarith
          have h5 : w'' * (2 * X'') ≤ w'' * (p : ℝ) ^ i :=
            mul_le_mul_of_nonneg_left (hp2.trans hpow) hw''.le
          linarith
        linarith [hw p hp i hiI]
    have hinner : ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ bp := by
      refine (Finset.sum_le_sum hi).trans ?_
      rw [Finset.sum_ite_eq']
      split_ifs
      · exact le_rfl
      · exact hbp0
    have h6 : 2 * Real.log p * ∑ i ∈ I p, max (at_ / (p : ℝ) ^ i - w p i) 0 ≤ 2 * Real.log p * bp :=
      mul_le_mul_of_nonneg_left hinner (by linarith)
    refine h6.trans ?_
    rw [hbp]
    split_ifs with hlt
    · have hlog : Real.log p ≤ Real.log (2 * X'') := Real.log_le_log hp0 (by nlinarith)
      have : 0 ≤ w'' * th := by positivity
      nlinarith
    · simp
  refine (Finset.sum_le_sum hper).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hcard := interval_count X'' (X'' * (1 + th))
    (s.filter (fun p : ℕ => (p : ℝ) < X'' * (1 + th))) (by nlinarith) (by
      intro n hn
      rw [Finset.mem_filter] at hn
      exact ⟨(hs n hn.1).le, hn.2.le⟩)
  have hnn : 0 ≤ 2 * Real.log (2 * X'') * (w'' * th) := by positivity
  have h7 := mul_le_mul_of_nonneg_right hcard hnn
  refine h7.trans (le_of_eq ?_)
  rw [← ha]; ring
end Formalism.LFunctionChainParameters.DeficitSplitLemmas
