-- Prove2me | solution 1 for Formalism.FrobeniusOrbits.SplitK.eq_of_ne_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:14:05.159603+00:00
-- url     : https://prove2.me/submissions/63122412-6337-4197-9386-6b3a4559271a

import Mathlib
import Definitions.Def_Formalism_FrobeniusOrbits_Statement
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_OddEqOneOfSubOneMem
import Definitions.Def_Formalism_TameInertiaTowers_CentralOrderTwo_DecompositionSubgroupIndex
import Definitions.Def_Formalism_FrobeniusOrbits_FrobeniusOrbitsProofs_SplitK
import Theorems.Thm_Formalism_FrobeniusOrbits_SplitK_apply_bK_of_ne
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
theorem _root_.solution (hd0 : 0 < d) (hb : b ^ 2 = -(d : L)) (σ τ : Kd b ≃ₐ[ℚ] Kd b) (hσ : σ ≠ 1)
    (hτ : τ ≠ 1) : σ = τ := by
  apply Kd_algEquiv_ext_of_apply_bK_eq
  rw [apply_bK_of_ne hd0 hb σ hσ, apply_bK_of_ne hd0 hb τ hτ]
end Formalism.FrobeniusOrbits.SplitK
