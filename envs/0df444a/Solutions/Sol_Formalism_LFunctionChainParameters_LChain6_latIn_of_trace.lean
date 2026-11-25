-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.latIn_of_trace
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T03:38:22.249377+00:00
-- url     : https://prove2.me/submissions/90dac4a9-4929-4bda-9b61-d36946624230

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
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_hsg
import Theorems.Thm_Formalism_LFunctionChainParameters_PrimeWindowSizeBounds_Facts_r2


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
theorem _root_.solution {I : Type} [Fintype I] {m : ℕ} (F : FamC I m) (Rw : Rows F.toFam) (x ε sg Gam C0S de : ℝ)
    (hT : F.TraceIn Rw x ε sg Gam C0S) (hx : 0 < x) (hsg0 : 0 < sg) (hsg : sg ≤ 1 / 20) (hE8 : E8 x ε ≤ sg / 2)
    (hde0 : 0 ≤ de) (hde4 : de ≤ 1 / 4) (hcor : ∑ u, ((F.d u : ℝ) - (F.r u : ℝ)) ≤ de * HilbertSchmidtNormSquare.Rs F.d)
    (w4 : ∀ u, F.Dstar / Gam ^ 2 / C0S ≤ (F.d u : ℝ)) :
    F.LatIn Rw sg Gam C0S (E7 x ε) := by
  obtain ⟨⟨r1, r2, r3, r4, r5, r6⟩, t1, t2, ⟨s1, s2, s3, s4, s5, s6, s7, s8⟩, ⟨w1, w2, w3⟩, hI,
    ⟨m1, m2, m3, m4, m5, m6⟩, ⟨i1, i2⟩⟩ := hT
  have h7 : E7 x ε < 1 := by
    unfold E7
    rw [Real.exp_lt_one_iff]
    have := Real.rpow_pos_of_pos hx (ε / 7)
    linarith
  exact ⟨r1, r2, r3, r4, r5, r6, t1, t2, de, E7 x ε, le_refl _, s1, s2, hsg0, hsg, w1, w2, w3, w4, s4, le_trans s5 hE8,
    le_trans s6 hE8, s7, le_trans s8 hE8, s3, hI, hde0, hde4, hcor, m1, m2, m3, i1, h7, i2, m4, m5, m6⟩
end Formalism.LFunctionChainParameters.LChain6
