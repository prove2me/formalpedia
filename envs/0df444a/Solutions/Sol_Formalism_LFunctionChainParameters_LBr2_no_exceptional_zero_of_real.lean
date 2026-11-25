-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBr2.no_exceptional_zero_of_real
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:27:26.367375+00:00
-- url     : https://prove2.me/submissions/81a1265f-7206-4fe9-85f8-b464bb285def

import Definitions.Def_Formalism_SizeWindowBrackets_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_GaloisMapComplexConjugation
import Definitions.Def_Formalism_LandauZeroFreeBounds_SiegelWalfiszAPOfSiegelLower
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction DirichletCharacter
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBr2
open Formalism Formalism.D5 Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBr2
theorem _root_.solution : NoExcOfReal := by
  rintro ⟨c, hc, hZ⟩
  refine ⟨min c (1 / 1000), lt_min hc (by norm_num), (min_le_right _ _).trans (by norm_num), ?_⟩
  intro q _ χ hreal
  refine ⟨by simp, by simp, ?_⟩
  intro s hs hz
  exfalso
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have h2le : (2 : ℝ) ≤ (q : ℝ) * (|s.im| + 2) := by
    have := abs_nonneg s.im
    nlinarith
  have hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * (|s.im| + 2)) := Real.log_le_log (by norm_num) h2le
  have hl2 := Real.log_two_gt_d9
  have hLpos : 0 < Real.log ((q : ℝ) * (|s.im| + 2)) := by linarith
  unfold Formalism.ZeroFreeDirichlet.InRegion at hs
  have hs' : Formalism.ZeroFreeDirichlet.InRegion c q s := by
    unfold Formalism.ZeroFreeDirichlet.InRegion
    have : min c (1 / 1000) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ c / Real.log ((q : ℝ) * (|s.im| + 2)) :=
      div_le_div_of_nonneg_right (min_le_left _ _) hLpos.le
    linarith
  obtain ⟨h2, -, him, -, -⟩ := hZ q χ s hs' hz
  have hsre : s = ((s.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
  have hσ : 1 - 1 / 400 < s.re := by
    have h3 : min c (1 / 1000) / Real.log ((q : ℝ) * (|s.im| + 2)) ≤ (1 / 1000) / (1 / 2) :=
      div_le_div₀ (by norm_num) (min_le_right _ _) (by norm_num) (by linarith)
    norm_num at h3
    linarith
  have := hreal h2 s.re hσ
  rw [← hsre] at this
  exact this hz.2
end Formalism.LFunctionChainParameters.LBr2
