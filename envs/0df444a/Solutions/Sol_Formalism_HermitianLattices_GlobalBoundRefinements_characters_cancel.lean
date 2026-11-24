-- Prove2me | solution 1 for Formalism.HermitianLattices.GlobalBoundRefinements.characters_cancel
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:50.796011+00:00
-- url     : https://prove2.me/submissions/51757d5b-5470-4efd-8d1c-4a66e3fac42e

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_InvNormSqConjRatioPowIdentities
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_PrimesInProgressionCountLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HadamardUnitDiagonalDetLeOne
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_SumWeightsOverPrimeLeHalfDegree
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ConditionIffDualEqFunctional
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_LengthQuotientBoundGeneral
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology ArithmeticFunction
noncomputable section
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GlobalBoundRefinements
namespace Formalism.HermitianLattices.GlobalBoundRefinements
theorem _root_.solution : CharactersCancelScalar := by
  intro A H inst1 inst2 χ m M M' g ϖ hg
  have hz : ∀ n : ℤ, (χ ^ n) ϖ = χ ϖ ^ n := by
    intro n
    first
    | rfl
    | simp
    | exact MonoidHom.zpow_apply χ n ϖ
  have key : (m * χ ^ (-M')) ϖ * (m⁻¹ * χ ^ M) ϖ = χ ϖ ^ (-g) := by
    rw [MonoidHom.mul_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, hz, hz,
      mul_mul_mul_comm, mul_inv_cancel, one_mul, ← zpow_add, ← hg]
    congr 1
    ring
  refine ⟨?_, ?_⟩
  · rw [key, zpow_neg, inv_inv]
  · rw [key, mul_inv_cancel]
end Formalism.HermitianLattices.GlobalBoundRefinements
