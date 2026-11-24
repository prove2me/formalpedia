-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_le_of_sub_one
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T11:05:30.187794+00:00
-- url     : https://prove2.me/submissions/61b2131f-7bff-4551-8ca3-686e13327db5

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_one
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_add_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (n : ℕ) (K : Matrix (Fin n) (Fin n) ℂ) :
    hsSq K ≤ (Real.sqrt n + hsNorm (K - 1)) ^ 2 := by
  have h := hsSq_add_le (1 : Matrix (Fin n) (Fin n) ℂ) (K - 1)
  rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + (K - 1) = K by abel] at h
  have h1 : hsNorm (1 : Matrix (Fin n) (Fin n) ℂ) = Real.sqrt n := by
    unfold hsNorm
    rw [hsSq_one]
  rwa [h1] at h
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
