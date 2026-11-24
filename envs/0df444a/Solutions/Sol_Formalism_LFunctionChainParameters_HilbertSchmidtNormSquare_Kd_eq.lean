-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.Kd_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T10:27:32.466469+00:00
-- url     : https://prove2.me/submissions/cd73c27d-5d97-4597-b4c2-dd667079c1a9

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
variable {ι : Type} [Fintype ι] {D : ℕ} {d : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (ga : ι → ℝ) (hga : ∀ u, 0 ≤ ga u) (u : ι) :
    Kd B ga u = ((ga u : ℝ) : ℂ) • ((B u)ᴴ * B u) := by
  unfold Kd Kp
  rw [Real.sqrt_mul_self (hga u)]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
