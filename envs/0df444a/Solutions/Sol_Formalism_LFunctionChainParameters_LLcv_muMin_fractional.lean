-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.LLcv.muMin_fractional
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T01:29:36.005009+00:00
-- url     : https://prove2.me/submissions/b68ec214-70df-49c6-990c-a25480d548a2

import Definitions.Def_Formalism_SizeWindowBrackets_LcvBaseChange
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_HermitianLattices_HermitianLatticesProofs_IndexBasic
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TruncatedLatticeHolds
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_log_absNorm_inv
import Theorems.Thm_Formalism_LFunctionChainParameters_LLcv_muMin_fractional_ge
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_fg
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_idealSmul_inv_cancel
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_ne_bot_of_rkK_pos
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_idealSmul
import Theorems.Thm_Formalism_LFunctionChainParameters_slopeLatticeData_rkK_pos


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
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.LLcv
open Formalism.HN Formalism.HermitianLatticesTheory Formalism.LFunctionChainParameters.slopeLatticeData
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
  [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι]
  [DecidableEq ι]
local notation "FI" => FractionalIdeal (nonZeroDivisors (𝓞 K)) K
namespace Formalism.LFunctionChainParameters.LLcv
theorem _root_.solution (b : Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : ∀ v, IsUnit (X v).det) {L : Submodule (𝓞 K) V} (hL : L.FG) (hL0 : L ≠ ⊥) {I : FI}
    (hI : I ≠ 0) :
    muMin (realize b X) (idealSmul (I : Submodule (𝓞 K) K) L) = muMin (realize b X) L -
      Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) := by
  have hfd : FiniteDimensional K V := Module.Finite.of_basis b
  have hIL0 : idealSmul (I : Submodule (𝓞 K) K) L ≠ ⊥ :=
    ne_bot_of_rkK_pos (by rw [rkK_idealSmul hI]; exact rkK_pos hL0)
  apply le_antisymm
  · have h := muMin_fractional_ge b X hX (idealSmul_fg I hL) hIL0 (inv_ne_zero hI)
    rw [idealSmul_inv_cancel hI, log_absNorm_inv] at h
    have e : -Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ) =
        -(Real.log ((FractionalIdeal.absNorm I : ℚ) : ℝ) / (Module.finrank ℚ K : ℝ)) := by ring
    rw [e] at h
    linarith
  · exact muMin_fractional_ge b X hX hL hL0 hI
end Formalism.LFunctionChainParameters.LLcv
