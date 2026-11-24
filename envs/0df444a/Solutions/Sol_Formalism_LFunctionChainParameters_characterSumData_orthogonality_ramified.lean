-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.characterSumData.orthogonality_ramified
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T11:43:08.15989+00:00
-- url     : https://prove2.me/submissions/ba5c9eef-83fc-47b5-a10f-243be0c0fd41

import Definitions.Def_Formalism_SizeWindowBrackets_FirstPrimeNeSecondPrime
import Definitions.Def_Formalism_ThickAverageLoss_ThickAverageProofs_Balance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_StronglyIrreducible
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_primitive_value_pow
import Theorems.Thm_Formalism_LFunctionChainParameters_characterSumData_ortho_coset

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset ArithmeticFunction
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.characterSumData
open Formalism Formalism.D5
open PB
variable {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H]
namespace Formalism.LFunctionChainParameters.characterSumData
theorem _root_.solution : OrthoRam (H := H) := by
  intro D p i hp hi g
  have hv : ∀ ψ : AddChar (E0 × H) ℂ, primVal D ψ (p ^ i) = cosetMean (D.inertia p) (i • D.frob p) ψ :=
    fun ψ => primitive_value_pow D ψ p i hp hi
  simp_rw [hv]
  convert ortho_coset (D.inertia p) (i • D.frob p) g
end Formalism.LFunctionChainParameters.characterSumData
