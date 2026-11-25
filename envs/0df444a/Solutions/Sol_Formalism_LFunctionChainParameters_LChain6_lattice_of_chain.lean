-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.lattice_of_chain
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:38:23.894175+00:00
-- url     : https://prove2.me/submissions/a783aa26-c05b-4ca5-adc3-e3ed1ef94063

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
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_chain_substitution
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_corollary_chain
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtUnitaryInvariance_frame_properties


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
theorem _root_.solution : LatOfChain := by
  intro I _ m F Rw sg Gam C0S delB hdual ⟨hX', hX, hcc, hccs, hN, hNs, hT1, hT2, de, del, hdel, hCh⟩
  obtain ⟨p1, p2, p3, -, p5, p6, -, p8, p9, p10, p11⟩ := HilbertSchmidtUnitaryInvariance.chain_substitution I F.Dall F.D F.D1 F.d F.r F.Pf F.Vr F.ga
    F.c F.Vrow F.U F.J F.J1 _ F.Y' F.Y F.Dstar sg F.η0 F.η1 F.e0 de del C0S Gam hCh
  have hDall : 0 < F.Dall := (HilbertSchmidtUnitaryInvariance.corollary_chain I F.Dall F.D F.D1 F.d F.r F.Pf F.Vr F.ga
    F.c F.Vrow F.U F.J F.J1 _ F.Y' F.Y F.Dstar sg F.η0 F.η1 F.e0 de del C0S Gam hCh).2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨-, c2, c3, c4, -, -, c7, -, c9, c10, c11, c12, c13, -, -, -, -, -, -, -, -, c22, -, -, c25, c26, -⟩ := hCh
  have hsum : F.Dall = F.D + F.D1 := (HilbertSchmidtUnitaryInvariance.frame_properties F.Dall F.D F.D1 F.J F.J1 c22).2.2.1
  have hn : (0 : ℝ) < (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) := by
    have : 0 < Fintype.card (Fin F.D ⊕ Fin F.D1) := by simp; omega
    exact_mod_cast this
  have hle : (Fintype.card (Fin F.D) : ℝ) ≤ (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) := by
    have : Fintype.card (Fin F.D) ≤ Fintype.card (Fin F.D ⊕ Fin F.D1) := by simp
    exact_mod_cast this
  have hdef : F.toFam.del = 1 - (Fintype.card (Fin F.D) : ℝ) / (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) := rfl
  have h1 : 1 - del ≤ (Fintype.card (Fin F.D) : ℝ) / (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) := by
    rw [le_div_iff₀ hn]; exact p11
  have h2 : (Fintype.card (Fin F.D) : ℝ) / (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) ≤ 1 := by
    rw [div_le_one hn]; exact hle
  have hd0 : 0 ≤ F.toFam.del := by rw [hdef]; linarith
  have hd1 : F.toFam.del ≤ del := by rw [hdef]; linarith
  have hd2 : (1 - F.toFam.del) * (Fintype.card (Fin F.D ⊕ Fin F.D1) : ℝ) ≤ (Fintype.card (Fin F.D) : ℝ) := by
    rw [hdef, sub_sub_cancel, div_mul_cancel₀ _ hn.ne']
  refine ⟨⟨⟨hX', hX, c26, c25, hcc, hccs, hN, hNs, p8, ?_, hT2, hd0, lt_of_le_of_lt hd1 p10, hd2, p6⟩, p1, fun _ => rfl, p2,
    c2, c3, c4, p3, c9, c10, c11, c12, c13, p5⟩, le_trans hd1 hdel, c7⟩
  intro i
  rintro _ ⟨φ, hφ, rfl⟩
  obtain ⟨β, hβ, hint⟩ := hT1 i φ hφ
  rw [hdual.2.2]
  exact ⟨β, hint, hβ⟩
end Formalism.LFunctionChainParameters.LChain6
