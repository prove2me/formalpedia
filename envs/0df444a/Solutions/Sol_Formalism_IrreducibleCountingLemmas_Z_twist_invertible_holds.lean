-- Prove2me | solution 1 for Formalism.IrreducibleCountingLemmas.Z.twist_invertible_holds
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T09:15:33.43589+00:00
-- url     : https://prove2.me/submissions/b28d98f1-009f-4b84-81af-0fa6f671aa0b

import Definitions.Def_Formalism_PadicSubsetSums_CentralIdempotents_PrimitiveRootFifteenSubOneUnit
import Mathlib
import Definitions.Def_Formalism_GaloisIrreducibility_NoSolvableTransitive
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Adjugate
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Mobius
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Window
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Koszul
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Parabolic
import Definitions.Def_Formalism_ResultantValuation_BoundedCubic
import Definitions.Def_Formalism_ResultantValuation_ResultantAdjugateProofs_Laplace
import Definitions.Def_Formalism_ResultantValuation_PrimePairDyadicDisjointAlt
import Definitions.Def_Formalism_PadicSubsetSums_StableGradedCounts_ZReuse

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Polynomial
open Formalism Formalism.IrreducibleCountingLemmas Formalism.IrreducibleCountingLemmas.Z
namespace Formalism.IrreducibleCountingLemmas.Z
theorem _root_.solution : TwistInvertible := by
  intro k V _ _ _ _ γ₀ c hc hne
  let L : Module.End k V := c⁻¹ • γ₀ - 1
  have hL : ∀ v, L v = c⁻¹ • γ₀ v - v := fun v => rfl
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro v hv
    rw [hL, sub_eq_zero] at hv
    have h2 : γ₀ v = c • v := by
      calc γ₀ v = c • (c⁻¹ • γ₀ v) := by rw [smul_smul, mul_inv_cancel₀ hc, one_smul]
        _ = c • v := by rw [hv]
    by_contra hv0
    exact hne (Module.End.hasEigenvalue_of_hasEigenvector
      ⟨Module.End.mem_eigenspace_iff.mpr h2, hv0⟩)
  have hbij : Function.Bijective L := ⟨hinj, LinearMap.injective_iff_surjective.mp hinj⟩
  exact hbij
end Formalism.IrreducibleCountingLemmas.Z
