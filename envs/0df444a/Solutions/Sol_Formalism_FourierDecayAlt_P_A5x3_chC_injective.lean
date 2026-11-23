-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.A5x3.chC_injective
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T01:29:36.454046+00:00
-- url     : https://prove2.me/submissions/a5bf85e9-4ffc-424f-a7c4-0b2258845542

import Definitions.Def_Formalism_HermitianCurvature_BlockKernelPropertiesOfSteps
import Definitions.Def_Formalism_DoubleCosetMeasures_LowerUnipotentOrbits_LowUniMulVecELast
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CharacterOrthogonalityDual
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_psiBar_apply
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_eq_zero_of_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_A5x3_chC_apply

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Matrix Formalism.DoubleCosetMeasures Formalism.FourierDecayAlt.A5
open scoped ComplexConjugate
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.A5x3
variable {K : Type} [CommRing K] (R : Subring K) (ψ : AddChar K ℂ)
variable {R ψ}
variable {C : Type} [AddCommGroup C] [Module R C]
namespace Formalism.FourierDecayAlt.P.A5x3
theorem _root_.solution (h : ∀ a : K, (∀ r ∈ R, ψ (a * r) = 1) ↔ a ∈ R) :
    Function.Injective (chC h : (C →ₗ[R] KR R) → AddChar C ℂ) := by
  intro μ ν hμν
  ext c
  rw [← sub_eq_zero]
  apply eq_zero_of_psi h
  intro r
  have h1 : chC h μ (r • c) = chC h ν (r • c) := by rw [hμν]
  rw [chC_apply, chC_apply, map_smul, map_smul] at h1
  rw [smul_sub, sub_eq_add_neg, ← psiBar_apply h, AddChar.map_add_eq_mul,
    AddChar.map_neg_eq_inv, psiBar_apply, psiBar_apply, h1]
  exact mul_inv_cancel₀ (AddChar.val_isUnit (psiBar h) _).ne_zero
end Formalism.FourierDecayAlt.P.A5x3
