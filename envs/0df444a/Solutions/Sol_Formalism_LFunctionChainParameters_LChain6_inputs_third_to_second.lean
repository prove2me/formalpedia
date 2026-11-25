-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LChain6.inputs_third_to_second
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T04:14:46.191828+00:00
-- url     : https://prove2.me/submissions/7172428b-7381-400b-ac5b-c7da23aa1898

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
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_lattice_of_chain
import Theorems.Thm_Formalism_LFunctionChainParameters_LChain6_mu_max_of_submodule

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
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] {W : H → Type} [∀ u0, Fintype (W u0)] {m : ℕ}
namespace Formalism.LFunctionChainParameters.LChain6
theorem _root_.solution : Inputs6cTo6b (H := H) (W := W) (m := m) := by
  intro D ell G C N TT T2 a w Fc Rw O η θ eK K logOm C0 cZ cL cE5 c5 C0S g₁ g₂
    ⟨hLat, hPl, hSub, hc28, hr, h5, hDiv, hS4, hS5, hT5, hLev, hRo, h8, h9, h10, h11, h12⟩
  have hL := fun u0 => lattice_of_chain (W u0) m (Fc u0) (Rw u0) (sgX G C.cHH) O.Gam C0S G.delBar
    (hDiv.1 u0).2.2.2 (hLat u0)
  refine ⟨fun u0 => (hL u0).1, hPl, fun u0 u => ?_, hc28, fun u0 u => ?_, h5, hDiv, hS4, hS5, hT5, hLev, hRo,
    fun u0 => ⟨(hL u0).2.1, (h8 u0).1, (h8 u0).2⟩, h9, h10, h11, h12⟩
  · obtain ⟨q1, q2, q3, -⟩ := (hPl u0).2.2.2.2.2 u
    refine mu_max_of_submodule (W u0) m (Fc u0) (hSub u0) u ((hLat u0).2.1 u) q1 q3 ?_
    intro h0
    have hb : (Fc u0).b u ⟨0, hr u0 u⟩ ∈ Submodule.span (Fc u0).K (((Fc u0).M u : Submodule _ _) : Set ((Fc u0).V u)) := by
      have := q2
      rw [this]; exact Submodule.mem_top
    rw [h0] at hb
    simp at hb
    exact ((Fc u0).b u).ne_zero _ hb
  · show (0 : ℝ) < (Fintype.card (Fin ((Fc u0).r u)) : ℝ)
    rw [Fintype.card_fin]
    exact_mod_cast hr u0 u
end Formalism.LFunctionChainParameters.LChain6
