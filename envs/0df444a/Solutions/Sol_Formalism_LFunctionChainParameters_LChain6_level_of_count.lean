-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.level_of_count
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T03:06:51.675053+00:00
-- url     : https://prove2.me/submissions/6e1c62b3-f219-47c4-af66-bb7bf2bfd04a

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
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_level_lower_of_count
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_level_sizes
import Theorems.Thm_Formalism_LFunctionChainParameters_SectionsFourToSixTransfer_pow_of_log


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
theorem _root_.solution : LevelOfCount (U0 := U0) (W := W) (Top := Top) (m := m) (f := f) := by
  intro D C cE5 c5 Gam X bN ⟨hE, hU, hV, hLW, hEW, hCW, hc1, hc2⟩ ⟨hm, hfb, hw, hlg, hmk, hc⟩ hL hb u0 u
  have h0 : 0 ≤ c5 := hCW.1
  have hP5 : BoundedBy' D c5 X := exact_coefficient_to_proposition D cE5 c5 X bN hEW hE hU h0 hc1
  have hlow : (m : ℝ) * D.L / 2 ≤ Real.log (D.T u0 u) :=
    level_lower_of_count (withGam D Gam) c5 Gam X hCW hP5 hLW hw hlg hmk hEW.2.2.2.2.1 hc u0 u
  have hf : 1 ≤ f := hEW.1
  have hG : 0 < Gam := lt_of_lt_of_le one_pos hCW.2.2.2.1
  have hTpos : 0 < D.T u0 u :=
    lt_of_lt_of_le (mul_pos (hLW u0 u).1 (Real.rpow_pos_of_pos hG _)) (hLW u0 u).2.1
  have hpow : D.b ^ ((m : ℝ) / 2) ≤ D.T u0 u :=
    (pow_of_log (m : ℝ) D.b (D.T u0 u) (by linarith) hTpos).1 (by rw [← hL]; exact hlow)
  have hm' : (6 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hb1 : D.b ≤ D.b ^ ((m : ℝ) / 2) := Real.self_le_rpow_of_one_le hb (by linarith)
  have hf' : (1 : ℝ) ≤ (f : ℝ) := by exact_mod_cast hf
  have h := level_sizes f m D.b (D.T u0 u) 2 hf hm hfb hpow (by linarith) le_rfl
  exact ⟨h.2.1, h.2.2.2, hlow⟩
end Formalism.LFunctionChainParameters.LChain6
