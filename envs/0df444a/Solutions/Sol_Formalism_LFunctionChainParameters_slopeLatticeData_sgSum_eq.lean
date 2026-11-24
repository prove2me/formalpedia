-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.sgSum_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:47:55.774365+00:00
-- url     : https://prove2.me/submissions/28dd1561-8053-459e-bfe1-0c427b5d3569

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_log_absNorm_idealPow

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
theorem _root_.solution (σ τ : FinPl K →₀ ℤ) :
    sgSum σ τ = -(2 * Real.log ((FractionalIdeal.absNorm (idealPow (-σ)) : ℚ) : ℝ) /
        (Module.finrank ℚ K : ℝ)) -
      2 * Real.log ((FractionalIdeal.absNorm (idealPow τ) : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  classical
  rw [log_absNorm_idealPow (-σ) (σ.support ∪ τ.support)
      (by rw [Finsupp.support_neg]; exact Finset.subset_union_left),
    log_absNorm_idealPow τ (σ.support ∪ τ.support) Finset.subset_union_right]
  unfold sgSum ell
  rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div, Finset.sum_div, ← Finset.sum_neg_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr (by congr) fun w _ => ?_
  rw [Finsupp.neg_apply, Int.cast_neg]
  ring
end Formalism.LFunctionChainParameters.slopeLatticeData
