-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.slopeLatticeData.slope_formula
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T02:38:01.09525+00:00
-- url     : https://prove2.me/submissions/10cd82c0-17d5-4b38-af2e-cb9c4f55831d

import Definitions.Def_Formalism_SizeWindowBrackets_SlopesHypothesisFinitePlaces
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DiscreteSpanOfLinIndep
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_SizeMu
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_HtGram
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_MuChar
import Definitions.Def_Formalism_HarderNarasimhan_HarderNarasimhanProofs_DualPl
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_WeightedMeanLemmaNeedsDegree
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_mono_right
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ne_bot_of_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_fg_of_le
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_index
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_absNorm_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muDef_fractional
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muMaxDef_mono
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_muMaxDef_fractional_le
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealPow_ne_zero
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_sgSum_eq

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
namespace Formalism.LFunctionChainParameters.slopeLatticeData
theorem _root_.solution : SlopeRelationsIndex := by
  intro K V ι _ _ _ _ _ _ _ _ _ _ b X hX σ τ M N hM hM0 hN hrk
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hτ := idealPow_ne_zero τ
  have hσ := idealPow_ne_zero (-σ)
  have hj := rkK_pos hM0
  set M1 := idealSmul ((idealPow τ : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) :
    Submodule (𝓞 K) K) M with hM1
  have hM1fg : M1.FG := idealSmul_fg _ hM
  have hM1rk : rkK M1 = rkK M := rkK_idealSmul hτ M
  have hNfg : N.FG := fg_of_le hM1fg hN
  have hN0 : N ≠ ⊥ := ne_bot_of_rkK_pos (hrk ▸ hj)
  have hN'0 : modLat σ N ≠ ⊥ :=
    ne_bot_of_rkK_pos (by unfold modLat; rw [rkK_idealSmul hσ, hrk]; exact hj)
  constructor
  · have hle : modLat σ N ≤ idealSmul ((idealPow (-σ) * idealPow τ :
        FractionalIdeal (nonZeroDivisors (𝓞 K)) K) : Submodule (𝓞 K) K) M := by
      rw [FractionalIdeal.coe_mul, idealSmul_mul]
      exact idealSmul_mono_right _ hN
    have h1 := muMaxDef_mono b X hX (idealSmul_fg _ hM) hle hN'0
    have h2 := muMaxDef_fractional_le b X hX hM hM0 (mul_ne_zero hσ hτ)
    rw [map_mul, Rat.cast_mul, Real.log_mul (absNorm_pos hσ).ne' (absNorm_pos hτ).ne'] at h2
    rw [sgSum_eq]
    have e : 2 * (Real.log ((FractionalIdeal.absNorm (idealPow (-σ)) : ℚ) : ℝ) +
        Real.log ((FractionalIdeal.absNorm (idealPow τ) : ℚ) : ℝ)) / (Module.finrank ℚ K : ℝ) =
        2 * Real.log ((FractionalIdeal.absNorm (idealPow (-σ)) : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) +
        2 * Real.log ((FractionalIdeal.absNorm (idealPow τ) : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
      ring
    rw [e] at h2
    linarith
  · unfold modLat
    rw [muDef_fractional b X hX hNfg hN0 hσ, muDef_index b X hX hM1fg hN hN0 (hrk.trans hM1rk.symm),
      hM1rk, hM1, muDef_fractional b X hX hM hM0 hτ, sgSum_eq]
    ring
end Formalism.LFunctionChainParameters.slopeLatticeData
