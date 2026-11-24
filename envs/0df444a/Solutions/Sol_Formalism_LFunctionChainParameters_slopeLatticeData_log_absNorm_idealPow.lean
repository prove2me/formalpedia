-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.log_absNorm_idealPow
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:31:58.283911+00:00
-- url     : https://prove2.me/submissions/5ac51ad5-e1ce-4dcc-ad04-d17bdc2cb158

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_finPl_ne_bot

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {K : Type} [Field K] [NumberField K]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (n : FinPl K →₀ ℤ) (U : Finset (FinPl K)) (hU : n.support ⊆ U) :
    Real.log ((FractionalIdeal.absNorm (idealPow n) : ℚ) : ℝ) =
      ∑ w ∈ U, (n w : ℝ) * Real.log (Ideal.absNorm w.1 : ℝ) := by
  have h1 : ((FractionalIdeal.absNorm (idealPow n) : ℚ) : ℝ) =
      ∏ w ∈ n.support, ((Ideal.absNorm w.1 : ℕ) : ℝ) ^ (n w) := by
    unfold idealPow Finsupp.prod
    rw [map_prod, Rat.cast_prod]
    refine Finset.prod_congr rfl fun w _ => ?_
    rw [map_zpow₀, FractionalIdeal.coeIdeal_absNorm, Rat.cast_zpow, Rat.cast_natCast]
  have hne : ∀ w : FinPl K, ((Ideal.absNorm w.1 : ℕ) : ℝ) ≠ 0 := fun w => by
    exact_mod_cast fun h => finPl_ne_bot w (Ideal.absNorm_eq_zero_iff.1 h)
  rw [h1, Real.log_prod (fun w _ => zpow_ne_zero _ (hne w))]
  rw [← Finset.sum_subset hU]
  · exact Finset.sum_congr rfl fun w _ => Real.log_zpow _ _
  · intro w _ hw
    rw [Finsupp.notMem_support_iff.1 hw]; simp
end Formalism.LFunctionChainParameters.slopeLatticeData
