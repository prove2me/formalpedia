-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.proj_idem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:34:58.475647+00:00
-- url     : https://prove2.me/submissions/24c1131f-aae1-4a21-9aa6-a07fe5c7d429

import Definitions.Def_Formalism_SizeWindowBrackets_TraceSquareAndDiagBounds
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf

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
theorem _root_.solution (V : Matrix m k ℂ) (hV : Vᴴ * V = 1) :
    (1 - V * Vᴴ) * (1 - V * Vᴴ) = 1 - V * Vᴴ := by
  have hP : V * Vᴴ * (V * Vᴴ) = V * Vᴴ := by
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc Vᴴ V, hV, Matrix.one_mul]
  simp only [sub_mul, mul_sub, one_mul, mul_one, hP]
  abel
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
