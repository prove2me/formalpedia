-- Prove2me | solution 1 for Formalism.DivisionValues.eigen_rational_hermitian_covolume
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-25T16:29:50.105319+00:00
-- url     : https://prove2.me/submissions/fc7953e2-11cb-448c-bd8d-6b1d4f1933d6

import Mathlib
import Definitions.Def_Formalism_QuotientMetricDivisors_EigenRatHermLcv
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ConjugateWeightLatticeOfGeneral
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_CommutingTwist
import Theorems.Thm_Formalism_DivisionValues_eigen_twist
import Theorems.Thm_Formalism_DivisionValues_cm_maximal_order_spec
import Theorems.Thm_Formalism_DivisionValues_covolume_via_basis
import Theorems.Thm_Formalism_DivisionValues_descent_cm_field
import Theorems.Thm_Formalism_DivisionValues_index_change_formula
import Theorems.Thm_Formalism_DivisionValues_ratHermLcv_of
import Theorems.Thm_Formalism_DivisionValues_restriction_rational_hermitian
import Theorems.Thm_Formalism_DivisionValues_semilocal_basis_exists


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
open ConjugateWeightGram FinitelyNonzeroLinear
namespace Formalism.DivisionValues
theorem _root_.solution : EigenRatHermLcv := by
  intro K _ _ _ _ K0 hK0 v0 hv0 n H X hX 𝒯 h𝒯 hcomm hadj Z Ω _ j hZ
  have hpos : ∀ v : InfinitePlace K, (H.map v.embedding).PosDef := fun v => by
    rw [← (hX.2 v).2]
    apply Matrix.PosDef.conjTranspose_mul_self
    rw [Matrix.mulVec_injective_iff_isUnit, Matrix.isUnit_nonsing_inv_iff,
      Matrix.isUnit_iff_isUnit_det]
    exact (hX.2 v).1
  have htw := eigen_twist K K0 hK0 v0 hv0 n H hX.1 hpos 𝒯 h𝒯 hcomm hadj Z Ω j hZ
  obtain ⟨d, z, hzli, hzspan, hzcm⟩ := descent_cm_field K n Z htw
  obtain ⟨hcmSub, hle, hstar, -⟩ := cm_maximal_order_spec K
  have hXcm : IsRatHerm (cmMax K) H X := ⟨fun i k => hle K0 hK0 (hX.1 i k), hX.2⟩
  obtain ⟨XT, hXT, hmaj, hform'⟩ :=
    restriction_rational_hermitian K (cmMax K) hcmSub hstar n H X hXcm d z hzli hzcm
  exact ⟨d, z, XT, hzli, hzspan, hzcm, hXT, hmaj, hform', fun T hT =>
    ratHermLcv_of covolume_via_basis index_change_formula semilocal_basis_exists K (cmMax K) hcmSub d
      (gramMat H z) XT hXT T hT⟩
end Formalism.DivisionValues
