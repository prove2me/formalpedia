-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LatticeToWeightTransfer.primitive_transfer
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:37.012591+00:00
-- url     : https://prove2.me/submissions/d627b041-53dd-49a4-b66a-e90cc1838555

import Definitions.Def_Formalism_SizeWindowBrackets_SlopeHypothesesRounded
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedSlopeExcessDecomposition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_SlopeInequalityOfLattices
import Theorems.Thm_Formalism_LFunctionChainParameters_UnitWeightPartition_deficit_bounds
import Theorems.Thm_Formalism_LFunctionChainParameters_UnitWeightPartition_truncatedLength_bound
import Theorems.Thm_Formalism_LFunctionChainParameters_UnitWeightPartition_unit_weight_partition


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LatticeToWeightTransfer
open Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds
variable {U0 : Type} [Fintype U0] {W : U0 → Type} [∀ u0, Fintype (W u0)]
  [∀ u0, Nonempty (W u0)] {Top : Type} [Fintype Top] {m f : ℕ}
variable {ι : Type} [DecidableEq ι]
variable (D : Data U0 W Top m f) (C : Consts) (Xpp cT : ℝ) (Q : ∀ u0, W u0 → PPrim ι m)
namespace Formalism.LFunctionChainParameters.LatticeToWeightTransfer
theorem _root_.solution : BridgePrim D Q := by
  intro h u0 u
  obtain ⟨hl, hdM, hT2, hT4, hdu, hsub, htauT, htau, hio, hG1, hT5, hlam, hlT, hsg, hRd, hmu, hmax,
    hMu, hMaxMu, hTa, hsmall, hmap, hfib, hiop⟩ := h u0 u
  obtain ⟨d1, d2, d3, d4⟩ := UnitWeightPartition.deficit_bounds f (D.T u0 u) (Q u0 u).dM (Q u0 u).du hdM hT2 hdu
  have hTpos : 0 < D.T u0 u := by linarith
  have hhalf : 2 * (f : ℝ) / D.T u0 u ≤ 1 / 2 := by
    rw [div_le_iff₀ hTpos]; linarith
  have hPT := UnitWeightPartition.truncatedLength_bound (Q u0 u).ST (Q u0 u).l (Q u0 u).len (Q u0 u).dM (Q u0 u).du
    (1 - (Q u0 u).du / (Q u0 u).dM) (Q u0 u).lam (D.T u0 u) (fun w hw => hl w (hsub hw)) hdM d2
    (le_trans d4 hhalf) d1 hlam hT5 hlT
  have hU := UnitWeightPartition.unit_weight_partition (Q u0 u).S (Q u0 u).Pr (Q u0 u).pr (Q u0 u).l (Q u0 u).io
    (Q u0 u).iop hmap hfib hiop
  exact ⟨⟨hl, hdM, d2, d3, d1, hsub, htauT, hio, hG1, hPT, hRd, hmu⟩,
    ⟨hMu, d4, hhalf, htau, hTa, hsmall, hU, le_refl _, le_refl _⟩,
    ⟨hl, hsg, hmax, hMaxMu⟩⟩
end Formalism.LFunctionChainParameters.LatticeToWeightTransfer
