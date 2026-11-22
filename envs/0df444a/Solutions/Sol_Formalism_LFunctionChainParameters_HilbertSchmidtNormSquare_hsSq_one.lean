-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.hsSq_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:52.617138+00:00
-- url     : https://prove2.me/submissions/d32174ce-8f03-4af0-ad97-b72a6cd11bf7

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
theorem _root_.solution (n : ℕ) : hsSq (1 : Matrix (Fin n) (Fin n) ℂ) = n := by
  have h : ∀ i j : Fin n, ‖(1 : Matrix (Fin n) (Fin n) ℂ) i j‖ ^ 2 = if i = j then 1 else 0 := by
    intro i j
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  unfold hsSq
  simp [h]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
