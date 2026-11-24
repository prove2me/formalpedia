-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_split
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T10:28:34.746241+00:00
-- url     : https://prove2.me/submissions/bf792418-b933-4a49-9aaf-7ceae7936789

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_eq_re
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_proj_herm
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_proj_idem

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
variable {m n k : Type} [Fintype m] [Fintype n] [Fintype k] [DecidableEq m] [DecidableEq k]
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) (M : Matrix m n ℂ) :
    hsSq M = hsSq (Vᴴ * M) + hsSq ((1 - V * Vᴴ) * M) := by
  have e1 : ((Vᴴ * M)ᴴ * (Vᴴ * M)).trace = (Mᴴ * (V * Vᴴ) * M).trace := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    simp only [Matrix.mul_assoc]
  have e2 : (((1 - V * Vᴴ) * M)ᴴ * ((1 - V * Vᴴ) * M)).trace
      = (Mᴴ * M).trace - (Mᴴ * (V * Vᴴ) * M).trace := by
    rw [Matrix.conjTranspose_mul, proj_herm V]
    rw [show Mᴴ * (1 - V * Vᴴ) * ((1 - V * Vᴴ) * M) = Mᴴ * ((1 - V * Vᴴ) * (1 - V * Vᴴ)) * M by
      simp only [Matrix.mul_assoc]]
    rw [proj_idem V hV, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.trace_sub]
  rw [hsSq_eq_re M, hsSq_eq_re (Vᴴ * M),
    hsSq_eq_re ((1 - V * Vᴴ) * M), e1, e2, Complex.sub_re]
  ring
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
