-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.algG
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:38.894475+00:00
-- url     : https://prove2.me/submissions/737d0960-d322-4424-9198-32216055344a

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_CongruenceTorsion
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferenceStableUnderAction
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_DifferentIdealConditions
import Definitions.Def_Formalism_FrobeniusOrbits_HostCorollaries
import Definitions.Def_Formalism_TameInertiaTowers_TowerFieldFoundations
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CongruenceSubgroupTorsionFree
import Theorems.Thm_Formalism_FrobeniusOrbits_galEquiv_apply
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.FrobeniusOrbits.galEquiv_apply
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.StabilizerLevels
open Formalism.HermitianLattices.StabilizerLevels.PfB
open NumberField IntermediateField Ideal IsDedekindDomain nonZeroDivisors
open scoped Pointwise
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition Formalism.HermitianLattices.FiltrationBoundaryCriterion
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution {G : Type*} [CommGroupWithZero G] (cB cB' s cC cC' : G) (h1 : cB' ≠ 0) (h2 : cC ≠ 0) :
    (cB * cB' * s)⁻¹ * (cC' * cB'⁻¹)⁻¹ = (cC * cC' * s)⁻¹ * (cC * cB⁻¹) := by
  simp only [mul_inv, inv_inv]
  calc cB⁻¹ * cB'⁻¹ * s⁻¹ * (cC'⁻¹ * cB') = (cB'⁻¹ * cB') * (cB⁻¹ * s⁻¹ * cC'⁻¹) := by ac_rfl
    _ = (cC⁻¹ * cC) * (cB⁻¹ * s⁻¹ * cC'⁻¹) := by rw [inv_mul_cancel₀ h1, inv_mul_cancel₀ h2]
    _ = _ := by ac_rfl
end Formalism.HermitianLattices.StabilizerLevels.PfB
