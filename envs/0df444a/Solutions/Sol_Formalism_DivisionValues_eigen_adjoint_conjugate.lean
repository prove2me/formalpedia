-- Prove2me | solution 1 for Formalism.DivisionValues.eigen_adjoint_conjugate
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T16:38:27.840183+00:00
-- url     : https://prove2.me/submissions/21c162c3-ad10-4883-b633-009ed19ee0bd

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_posDef_all
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_adj_matrix
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_map_conjTranspose_twist
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_map_twist_of_mem
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_vec_zero_of_form
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_form_adj
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_form_smul_left
import Theorems.Thm_Formalism_DivisionValues_FinitelyNonzeroLinear_form_smul_right

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder
noncomputable section
open Formalism Formalism.DivisionValues
open FinitelyNonzeroLinear
namespace Formalism.DivisionValues
theorem _root_.solution : EigenAdjConj := by
  intro K _ _ _ K0 hK0 n H hH hpos 𝒯 h𝒯 σ χ x hx hx0 T hT T' hT' hadj
  have hM : Tᴴ * H = H * T' := FinitelyNonzeroLinear.adj_matrix hadj
  have hPD := FinitelyNonzeroLinear.posDef_all hpos σ
  have hmap : (T.map σ)ᴴ * H.map σ = H.map σ * T'.map σ := by
    have := congrArg (fun X => X.map σ) hM
    simp only [Matrix.map_mul] at this
    rwa [FinitelyNonzeroLinear.map_conjTranspose_twist, FinitelyNonzeroLinear.map_twist_of_mem hK0 σ T (h𝒯 T hT)] at this
  have hxe : ∀ S ∈ 𝒯, (S.map σ).mulVec x = χ S • x := hx
  have hf := FinitelyNonzeroLinear.form_adj hmap x x
  rw [hxe T hT, hxe T' hT', FinitelyNonzeroLinear.form_smul_left, FinitelyNonzeroLinear.form_smul_right] at hf
  have hq : star x ⬝ᵥ H.map σ *ᵥ x ≠ 0 := fun h0 => hx0 (FinitelyNonzeroLinear.vec_zero_of_form hPD x h0)
  exact (mul_right_cancel₀ hq hf).symm
end Formalism.DivisionValues
