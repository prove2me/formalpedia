-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.muDef_eq_log
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:40:15.373176+00:00
-- url     : https://prove2.me/submissions/b62216b1-ac08-4d54-901b-dd55e2635036

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_pos
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
open Module NumberField
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.slopeLatticeData
open Formalism.HN Formalism.HermitianLatticesTheory
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) :
    muDef b X L = -(2 * Real.log (ht b X L)) / ((Module.finrank ℚ K : ℝ) * (rkK L : ℝ)) := by
  have h := (size_maximal_slope K V ι b X hX L hL hL0).2.1
  rw [h, size, Real.log_rpow (ht_pos b X hX hL), sizeMu_finrank_eq K]
  push_cast
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hj : (rkK L : ℝ) ≠ 0 := by exact_mod_cast (rkK_pos hL0).ne'
  have hf : (nPl K : ℝ) ≠ 0 := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this.ne'
  field_simp
end Formalism.LFunctionChainParameters.slopeLatticeData
