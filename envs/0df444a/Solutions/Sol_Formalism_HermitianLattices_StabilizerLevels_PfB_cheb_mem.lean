-- Prove2me | solution 1 for Formalism.HermitianLattices.StabilizerLevels.PfB.cheb_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T19:14:39.817329+00:00
-- url     : https://prove2.me/submissions/8f5cf9fc-713b-4350-9178-3a32461bf8be

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
open NumberField IntermediateField
open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition
variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}
namespace Formalism.HermitianLattices.StabilizerLevels.PfB
theorem _root_.solution (hζ0 : ζ ≠ 0) (j : ℕ) : ζ ^ j + ζ⁻¹ ^ j ∈ F1 ζ ∧ ζ ^ (j + 1) + ζ⁻¹ ^ (j + 1) ∈ F1 ζ := by
  have hθ : ζ + ζ⁻¹ ∈ F1 ζ := mem_adjoin_simple_self ℚ _
  induction j with
  | zero =>
    refine ⟨?_, by simpa using hθ⟩
    have : ζ ^ 0 + ζ⁻¹ ^ 0 = ((2 : ℕ) : L) := by norm_num
    rw [this]; exact _root_.natCast_mem _ _
  | succ j ih =>
    refine ⟨ih.2, ?_⟩
    have : ζ ^ (j + 1 + 1) + ζ⁻¹ ^ (j + 1 + 1) =
        (ζ + ζ⁻¹) * (ζ ^ (j + 1) + ζ⁻¹ ^ (j + 1)) - (ζ ^ j + ζ⁻¹ ^ j) := by
      have h1 : ζ * ζ⁻¹ = 1 := mul_inv_cancel₀ hζ0
      linear_combination (-(ζ ^ j) - ζ⁻¹ ^ j) * h1
    rw [this]
    exact sub_mem (mul_mem hθ ih.2) ih.1
end Formalism.HermitianLattices.StabilizerLevels.PfB
