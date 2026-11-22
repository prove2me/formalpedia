-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsNorm_le_of_sq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:52.568416+00:00
-- url     : https://prove2.me/submissions/afa1aa5b-bcdb-40d3-870b-152ec42872d6

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
variable {m n : Type} [Fintype m] [Fintype n]
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (M : Matrix m n ℂ) {e x : ℝ} (he : 0 ≤ e) (h : hsSq M ≤ e * x) :
    hsNorm M ≤ Real.sqrt e * Real.sqrt x := by
  unfold hsNorm
  rw [← Real.sqrt_mul he]
  exact Real.sqrt_le_sqrt h
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
