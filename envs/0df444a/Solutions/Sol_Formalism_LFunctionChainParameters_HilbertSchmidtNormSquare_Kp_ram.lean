-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare.Kp_ram
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:52.651631+00:00
-- url     : https://prove2.me/submissions/c9e28cb4-a147-44c3-b495-c45bc451db15

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
variable {ι : Type} [Fintype ι] {D : ℕ} {d r : ι → ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
theorem _root_.solution (B : ∀ u, Matrix (Fin D) (Fin (d u)) ℂ) (V : ∀ u, Matrix (Fin (d u)) (Fin (r u)) ℂ)
    (ga : ι → ℝ) (u u' : ι) : Kp (Bram B V) ga u u' = (V u)ᴴ * Kp B ga u u' * V u' := by
  simp only [Kp, Bram, Matrix.conjTranspose_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.mul_assoc]
end Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
