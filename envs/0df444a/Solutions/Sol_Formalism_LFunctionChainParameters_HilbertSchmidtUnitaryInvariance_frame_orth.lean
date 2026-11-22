-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance.frame_orth
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:54:55.200621+00:00
-- url     : https://prove2.me/submissions/e8c4f7e5-0fe0-47a9-bd2e-a93e9fd9dc7a

import Definitions.Def_Formalism_SizeWindowBrackets_MatrixFamilyBoundsOfCardEqCeil
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsOrthonormalFrameComplement

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Module NumberField
open scoped ComplexOrder
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare
noncomputable section
variable {Dall D D1 : ℕ}
namespace Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
theorem _root_.solution (J : Matrix (Fin Dall) (Fin D) ℂ) (J1 : Matrix (Fin Dall) (Fin D1) ℂ)
    (h : OrthFrame J J1) : Jᴴ * J1 = 0 := by
  obtain ⟨h1, h2, h3⟩ := h
  have e : Jᴴ * (J * Jᴴ + J1 * J1ᴴ) * J1 = Jᴴ * J1 + Jᴴ * J1 := by
    rw [Matrix.mul_add, Matrix.add_mul]
    have a1 : Jᴴ * (J * Jᴴ) * J1 = (Jᴴ * J) * (Jᴴ * J1) := by simp only [Matrix.mul_assoc]
    have a2 : Jᴴ * (J1 * J1ᴴ) * J1 = (Jᴴ * J1) * (J1ᴴ * J1) := by simp only [Matrix.mul_assoc]
    rw [a1, a2, h1, h2, Matrix.one_mul, Matrix.mul_one]
  rw [h3, Matrix.mul_one] at e
  calc Jᴴ * J1 = (Jᴴ * J1 + Jᴴ * J1) - Jᴴ * J1 := by abel
    _ = Jᴴ * J1 - Jᴴ * J1 := by rw [← e]
    _ = 0 := sub_self _
end Formalism.LFunctionChainParameters.HilbertSchmidtUnitaryInvariance
