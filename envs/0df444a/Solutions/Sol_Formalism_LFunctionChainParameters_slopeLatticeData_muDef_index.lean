-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.muDef_index
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:48:22.045386+00:00
-- url     : https://prove2.me/submissions/6166225a-47d9-4b69-af91-4b0a2c5de201

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_fg_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_index
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_eq_log

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
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {M N : Submodule (𝓞 K) V} (hM : M.FG) (hNM : N ≤ M)
    (hN0 : N ≠ ⊥) (hrk : rkK N = rkK M) :
    muDef b X N = muDef b X M - 2 * Real.log (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) /
      ((Module.finrank ℚ K : ℝ) * (rkK M : ℝ)) := by
  have hN : N.FG := fg_of_le hM hNM
  have hM0 : M ≠ ⊥ := fun h => hN0 (eq_bot_iff.2 (h ▸ hNM))
  have hi := ht_index b X hX hM hNM hrk
  have hc : (N.toAddSubgroup.relIndex M.toAddSubgroup : ℝ) ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hi
    exact (ht_pos b X hX hN).ne' hi
  rw [muDef_eq_log b X hX hN hN0, muDef_eq_log b X hX hM hM0, hi, hrk,
    Real.log_mul (ht_pos b X hX hM).ne' hc]
  ring
end Formalism.LFunctionChainParameters.slopeLatticeData
