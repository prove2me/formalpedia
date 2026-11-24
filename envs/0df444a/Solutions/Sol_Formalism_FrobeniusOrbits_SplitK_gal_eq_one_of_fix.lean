-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.gal_eq_one_of_fix
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:08:41.760783+00:00
-- url     : https://prove2.me/submissions/d0341070-a7eb-4261-95ff-316e41a6a4b1

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
namespace Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
private theorem isIntegral_b : IsIntegral ℚ b := by
  first
  | exact IsIntegral.of_finite ℚ b
  | exact Algebra.IsIntegral.isIntegral b
private theorem Kd_algEquiv_ext_of_apply_bK_eq (σ τ : Kd b ≃ₐ[ℚ] Kd b) (h : σ (bK b) = τ (bK b)) : σ = τ := by
  have hint : IsIntegral ℚ b := isIntegral_b
  have key : (σ : Kd b →ₐ[ℚ] Kd b) = (τ : Kd b →ₐ[ℚ] Kd b) := by
    apply (IntermediateField.adjoin.powerBasis hint).algHom_ext
    first
    | exact h
    | (rw [IntermediateField.adjoin.powerBasis_gen]; exact h)
    | (simp only [IntermediateField.adjoin.powerBasis_gen, AlgEquiv.coe_algHom]; exact h)
  exact AlgEquiv.ext fun x => AlgHom.congr_fun key x
end Formalism.FrobeniusOrbits.SplitK
namespace Formalism.FrobeniusOrbits
end Formalism.FrobeniusOrbits
end
end

set_option autoImplicit false
open NumberField IntermediateField Ideal
open scoped Pointwise
noncomputable section
open Formalism Formalism.FrobeniusOrbits Formalism.FrobeniusOrbits.SplitK
open Formalism.TwoAdicCyclotomicDecomposition
variable {L : Type} [Field L] [NumberField L] {b : L} {d : ℕ}
namespace Formalism.FrobeniusOrbits.SplitK
theorem _root_.solution (σ : Kd b ≃ₐ[ℚ] Kd b) (h : σ (bK b) = bK b) : σ = 1 := by
  apply Kd_algEquiv_ext_of_apply_bK_eq σ 1
  first
  | (rw [h]; rfl)
  | simpa using h
  | (rw [AlgEquiv.one_apply]; exact h)
end Formalism.FrobeniusOrbits.SplitK
