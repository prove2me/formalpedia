-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_fractional_le
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T02:28:59.19119+00:00
-- url     : https://prove2.me/submissions/bddbed30-bdbb-407a-a0c3-89b741ee9ec7

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_mono_right
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_inv_cancel
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_cancel_inv
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ne_bot_of_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_fg_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_fractional
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_le_muMaxDef
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muMaxDef_le

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
    muMaxDef b X (idealSmul (I : Submodule (𝓞 K) K) L) ≤ muMaxDef b X L -
      2 * Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)
  refine muMaxDef_le b X hIL0 fun Q hQ hQ0 => ?_
  have hQfg : Q.FG := fg_of_le (idealSmul_fg I hL) hQ
  have hI' : I⁻¹ ≠ 0 := inv_ne_zero hI
  set Q' := idealSmul ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) Q
    with hQ'
  have hQ'L : Q' ≤ L := by
    have := idealSmul_mono_right
      ((I⁻¹ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) hQ
    rwa [idealSmul_inv_cancel hI] at this
  have hQ'0 : Q' ≠ ⊥ := ne_bot_of_rkK_pos (by rw [hQ', rkK_idealSmul hI']; exact rkK_pos hQ0)
  have hQeq : Q = idealSmul (I : Submodule (𝓞 K) K) Q' := (idealSmul_cancel_inv hI Q).symm
  rw [hQeq, muDef_fractional b X hX (fg_of_le hL hQ'L) hQ'0 hI]
  have := muDef_le_muMaxDef b X hX hL hQ'L hQ'0
  linarith
end Formalism.LFunctionChainParameters.slopeLatticeData
