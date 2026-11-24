-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.index_finsupp
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T11:26:47.635828+00:00
-- url     : https://prove2.me/submissions/2f969b9a-b36d-4cd3-af62-328f9db65708

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_card_eq_prod_locLen

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
theorem _root_.solution {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module (𝓞 K) V]
    (A B : Submodule (𝓞 K) V) (h : B.toAddSubgroup.relIndex A.toAddSubgroup ≠ 0) :
    ∃ k : FinPl K →₀ ℕ, (∀ w : FinPl K, lenAt w A B = (k w : ℕ∞)) ∧
      B.toAddSubgroup.relIndex A.toAddSubgroup = k.prod fun w j => Ideal.absNorm w.1 ^ j := by
  have h' : Nat.card (A ⧸ B.comap A.subtype) ≠ 0 := h
  have hfin : Finite (A ⧸ B.comap A.subtype) := Nat.finite_of_card_ne_zero h'
  obtain ⟨k, hk, hc⟩ := card_eq_prod_locLen (R := 𝓞 K) _ (A ⧸ B.comap A.subtype) rfl
  refine ⟨k, hk, ?_⟩
  change Nat.card (A ⧸ B.comap A.subtype) = _
  rw [hc]
  refine Finsupp.prod_congr fun w _ => ?_
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
end Formalism.LFunctionChainParameters.slopeLatticeData
