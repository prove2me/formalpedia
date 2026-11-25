-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.mu_max_of_submodule
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:15:19.999518+00:00
-- url     : https://prove2.me/submissions/f0d62991-82fb-4fba-bcfd-01b786cd2e3e

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesFromSizeAndCount
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChainLatticeSizesModelEventually
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PrimeCongruenceConditions
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SecondPriceSumWeightsUncovered
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_DisplayedInequalitySharpHalf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PSmall
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LocalizationStructureHolds
import Definitions.Def_Formalism_LandauZeroFreeBounds_ExceptionalZeroBounds_ZetaNegReal
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ChiEightNoRealZeroHypothesis
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_AnalyticFirstToLatticeDiscriminant
import Theorems.Thm_Formalism_HN_slope_inequality_mean


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix IsDedekindDomain
open Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LChain6
open Formalism Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr Formalism.LFunctionChainParameters.LChain
  Formalism.LFunctionChainParameters.LChain2 Formalism.LFunctionChainParameters.LHost Formalism.LFunctionChainParameters.LBr2 Formalism.LFunctionChainParameters.LBrDiv Formalism.LFunctionChainParameters.SectionsFourToSixTransfer
namespace Formalism.LFunctionChainParameters.LChain6
theorem _root_.solution : MuMaxOfSub := by
  intro I m F hS u hX hM hMf hne
  obtain ⟨hXf, hinj, hht, hmap⟩ := hS u
  have hle : (F.M u).map ((F.j u).restrictScalars (𝓞 F.K)) ≤ F.Mf u := by rw [hmap]; exact inf_le_left
  have hne' : (F.M u).map ((F.j u).restrictScalars (𝓞 F.K)) ≠ ⊥ := by
    intro h0
    apply hne
    rw [eq_bot_iff]
    intro y hy
    have h1 : (F.j u) y ∈ (F.M u).map ((F.j u).restrictScalars (𝓞 F.K)) := ⟨y, hy, rfl⟩
    rw [h0, Submodule.mem_bot] at h1
    exact (Submodule.mem_bot _).2 (hinj (h1.trans (map_zero _).symm))
  have h := ((slope_inequality_mean F.K (F.V u) (Fin (F.r u)) (F.Vf u) (Fin (F.d u)) (F.b u) (F.X u) (F.bf u) (F.Xf u) hX hXf
    (F.j u) (F.M u) hM hne').2 (F.Mf u) hMf hle).2 hinj.injOn
  linarith
end Formalism.LFunctionChainParameters.LChain6
