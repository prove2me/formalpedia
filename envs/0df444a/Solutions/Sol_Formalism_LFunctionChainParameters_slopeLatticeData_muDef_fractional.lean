-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.muDef_fractional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T01:48:54.065206+00:00
-- url     : https://prove2.me/submissions/70905d4e-dced-4485-9550-493704d567aa

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ne_bot_of_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_eq_log
import Theorems.Thm_P2M_Formalism_LFunctionChainParameters_slopeLatticeData_finrank_pos__952bcff0eee0
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ht_fractional
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_absNorm_pos

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
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥)
    {I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K} (hI : I ≠ 0) :
    muDef b X (idealSmul (I : Submodule (𝓞 K) K) L) = muDef b X L -
      2 * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hj := rkK_pos hL0
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact hj)
  rw [muDef_eq_log b X hX (idealSmul_fg I hL) hIL0, muDef_eq_log b X hX hL hL0,
    ht_fractional b X hX hL hI, rkK_idealSmul hI,
    Real.log_mul (ht_pos b X hX hL).ne' (pow_ne_zero _ (absNorm_pos hI).ne'), Real.log_pow]
  have hj' : (rkK L : ℝ) ≠ 0 := by exact_mod_cast hj.ne'
  have hq : (Module.finrank ℚ K : ℝ) ≠ 0 := (finrank_pos' (K := K)).ne'
  field_simp
  ring
end Formalism.LFunctionChainParameters.slopeLatticeData
