-- Prove2me | solution 1 for Deduction.CharacterBalance.ramifiedPrimeTerm_eq_zero_of_lt_ramifiedPrime
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:32:41.917919+00:00
-- url     : https://prove2.me/submissions/a30668e1-4c3f-44d2-af4f-2ddc35ace0eb

import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_SplitInertia
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Development_AutomorphicArithmetic_DedekindLFunctions_LandauTheorems_ChBalance
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_max_zero_of_gt


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset
noncomputable section
open Deduction
open Deduction.CH Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
open Deduction.CharacterBalance
open ArithmeticFunction Formalism.LFunctionChainParameters.characterSumData.PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Deduction.CharacterBalance
theorem _root_.solution (D : ArithData H) {S0 : Finset ℕ} (hD : HostFactsS D S0) {N : ℕ} {a : ℝ} {t : H} {w : E0 × H → ℝ}
    (hw : ∀ ρ, InPhi ρ → 0 < w ρ) (hN : ∀ ρ, InPhi ρ → a / w ρ ≤ N) (hdN : N < D.d) :
    askD D N a t w = 0 := by
  classical
  unfold askD
  refine Finset.sum_eq_zero (fun i hi => Finset.sum_eq_zero (fun g hg => ?_))
  have hg' := (Finset.mem_filter.1 hg).2.2
  simp only [Finset.mem_Icc] at hi
  apply max_zero_of_gt hw hN hg'
  have h1 : (D.d : ℝ) ≤ (D.d : ℝ) ^ i := by
    have : (1 : ℝ) ≤ D.d := by exact_mod_cast hD.d_prime.one_lt.le
    calc (D.d : ℝ) = (D.d : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (D.d : ℝ) ^ i := pow_le_pow_right₀ this hi.1
  have h2 : (N : ℝ) < D.d := by exact_mod_cast hdN
  linarith
end Deduction.CharacterBalance
