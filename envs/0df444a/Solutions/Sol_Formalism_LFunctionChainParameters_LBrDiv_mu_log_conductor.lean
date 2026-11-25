-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LBrDiv.mu_log_conductor
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:44:00.007155+00:00
-- url     : https://prove2.me/submissions/07ce38dc-315b-470d-8521-d66a4841dcef

import Definitions.Def_Formalism_SizeWindowBrackets_SBrDiv
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_LevelOfCongruence
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_Rerealize
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_PBrDiv
import Theorems.Thm_Formalism_LFunctionChainParameters_LBrDiv_ne_bot_of_span
import Theorems.Thm_Formalism_HN_place_lattice_structure
import Theorems.Thm_Formalism_HN_sizeMu_finrank_eq
import Theorems.Thm_Formalism_HN_size_maximal_slope


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
theorem _root_.solution : MuLcv := by
  intro K _ _ _ _ D hD X hX R hR
  have : Nonempty (Fin D) := ⟨⟨0, hD⟩⟩
  have hR0 : R ≠ ⊥ := ne_bot_of_span (Pi.basisFun K (Fin D)) R hR.span_eq_top
  obtain ⟨_, a2, _⟩ := size_maximal_slope K (Fin D → K) (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg hR0
  have hpos : 0 < ht (Pi.basisFun K (Fin D)) X R :=
    (place_lattice_structure K _ (Fin D) (Pi.basisFun K (Fin D)) X hX R hR.fg).2.2
  have hrk : rkK R = D := by
    unfold rkK
    rw [hR.span_eq_top, finrank_top]
    simp
  have hn : (Module.finrank ℚ K : ℝ) = 2 * (nPl K : ℝ) := by
    have := sizeMu_finrank_eq K
    exact_mod_cast this
  rw [a2]
  unfold size lcv
  rw [Real.log_rpow hpos, hrk, hn]
  have hD' : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
  have hnp : (nPl K : ℝ) ≠ 0 := by
    have h1 : (0 : ℝ) < (Module.finrank ℚ K : ℝ) := by exact_mod_cast Module.finrank_pos
    intro h0
    rw [hn, h0] at h1
    simp at h1
  field_simp
end Formalism.LFunctionChainParameters.LBrDiv
