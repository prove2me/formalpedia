-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.index_eq_length
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:15:12.970515+00:00
-- url     : https://prove2.me/submissions/613100db-34c4-4006-bfff-fc47b50f8c50

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_index_finsupp

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
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution : IndexLen := by
  intro K V _ _ _ _ A B h
  obtain ⟨k, hk, hc⟩ := index_finsupp A B h
  refine ⟨fun w => by rw [hk]; exact ENat.natCast_ne_top _, ?_, ?_⟩
  · refine k.support.finite_toSet.subset fun w hw => ?_
    rw [Function.mem_support, hk] at hw
    rw [Finset.mem_coe, Finsupp.mem_support_iff]
    exact_mod_cast hw
  · rw [hc, finprod_eq_prod_of_mulSupport_subset (s := k.support)]
    · refine Finset.prod_congr rfl fun w _ => ?_
      rw [hk, ENat.toNat_natCast]
    · intro w hw
      rw [Function.mem_mulSupport, hk, ENat.toNat_natCast] at hw
      rw [Finset.mem_coe, Finsupp.mem_support_iff]
      intro h0
      rw [h0, pow_zero] at hw
      exact hw rfl
end Formalism.LFunctionChainParameters.slopeLatticeData
