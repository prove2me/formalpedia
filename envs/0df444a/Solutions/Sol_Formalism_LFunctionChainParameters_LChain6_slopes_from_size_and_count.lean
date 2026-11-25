-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.slopes_from_size_and_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T03:51:35.368956+00:00
-- url     : https://prove2.me/submissions/97529e6a-120d-42f2-9980-603feb21eb71

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
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_exact_coefficient_to_proposition
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_joint_four_five
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_proposition_to_log_t_upper


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
variable {U0 : Type} {W : U0 → Type} {Top : Type} [Fintype Top] {m f : ℕ}
namespace Formalism.LFunctionChainParameters.LChain6
theorem _root_.solution : SlopesFromSizeAndCount (U0 := U0) (W := W) (Top := Top) (m := m) (f := f) := by
  intro D C cZ cL cE5 c5 Sc LZ Gam X bN ⟨hZ, hZW, hcS⟩ ⟨hE, hU, hV, hLW, hEW, hCW, hc1, hc2⟩
  have h0 : 0 ≤ c5 := hCW.1
  have hP5 : BoundedBy' D c5 X := exact_coefficient_to_proposition D cE5 c5 X bN hEW hE hU h0 hc1
  have hJ := joint_four_five (withGam D Gam) C cZ cL Sc LZ c5 Gam X hZW hZ hCW hP5 hV hLW hcS hc2
  exact ⟨hJ.1, hJ.2, proposition_to_log_t_upper (withGam D Gam) c5 Gam X hCW hP5 hLW⟩
end Formalism.LFunctionChainParameters.LChain6
