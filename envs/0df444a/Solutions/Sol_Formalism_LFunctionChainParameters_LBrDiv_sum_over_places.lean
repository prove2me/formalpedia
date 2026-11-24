-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.sum_over_places
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:45:38.986552+00:00
-- url     : https://prove2.me/submissions/d49898c3-3889-42c9-9c85-f6902ce55701

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_plOf_bijective

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LBrDiv
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain2
namespace Formalism.LFunctionChainParameters.LBrDiv
theorem _root_.solution : SumOverPlaces := by
  intro K _ _ S φ
  have hb := plOf_bijective K
  constructor
  · refine (S.finite_toSet.preimage hb.1.injOn).subset ?_
    intro w hw
    by_contra hn
    apply hw
    have : plOf w ∉ S := hn
    simp [this]
  · set g : slopeLatticeData.FinPl K → ℝ := fun v => slopeLatticeData.ell v * (if v ∈ S then ramE v * φ v else 0) with hg
    have h1 : (∑ᶠ w : HeightOneSpectrum (𝓞 K),
        lw w * (if plOf w ∈ S then ramE (plOf w) * φ (plOf w) else 0)) = ∑ᶠ v, g v :=
      finsum_comp_equiv (Equiv.ofBijective plOf hb) (f := g)
    rw [h1, finsum_eq_sum_of_support_subset (s := S)]
    · refine Finset.sum_congr rfl fun w hw => ?_
      simp only [hg, hw, if_true, lE]
      ring
    · intro v hv
      by_contra hn
      apply hv
      have : v ∉ S := hn
      simp [hg, this]
end Formalism.LFunctionChainParameters.LBrDiv
