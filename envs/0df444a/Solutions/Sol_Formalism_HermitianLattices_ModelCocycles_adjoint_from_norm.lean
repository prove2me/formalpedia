-- Prove2me | solution 1 for Formalism.HermitianLattices.ModelCocycles.adjoint_from_norm
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:48:29.903809+00:00
-- url     : https://prove2.me/submissions/9993b7aa-e19e-4446-91df-87c408cfb96a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ModelCocycleExponent
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_TeichmullerUnitAllPrimes

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.ModelCocycles
open Finset Formalism.HermitianLattices.IntegralLatticeDensity
namespace Formalism.HermitianLattices.ModelCocycles
theorem _root_.solution : AdjointFromNorm := by
  intro Z O M Q _ _ _ _ _ _ _ _ φ nm hnm hlin α hα a b
  have h1 : ∀ a b', cob φ ((α : O) • a) ((α : O) • b') = nm α • cob φ a b' := by
    intro a b'; unfold cob; rw [← smul_add, hα, hα, hα, smul_sub, smul_sub]
  have h2 := h1 a ((↑α⁻¹ : O) • b)
  rw [smul_smul, Units.mul_inv, one_smul, ← hlin, hnm, smul_smul, mul_assoc, Units.mul_inv, mul_one] at h2
  exact h2
end Formalism.HermitianLattices.ModelCocycles
