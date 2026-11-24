-- Prove2me | solution 1 for Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.leftCoeff_rename_mul
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:12:20.606302+00:00
-- url     : https://prove2.me/submissions/21bf0ffc-bf58-45e5-b983-66e960972625

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_GlobalTheory_GL6_LinearIndependentProdRenameOfCard
import Theorems.Thm_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inl
import Theorems.Thm_P2M_Formalism_L2_GlobalTheoryTheory_LocalLatticeBases_sumAlgEquiv_rename_inr_eq_C__b87c83100f40

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.GlobalTheoryTheory Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
open MvPolynomial
variable {K : Type*} [Field K] {S₁ S₂ : Type*}
namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
theorem _root_.solution (m : S₁ →₀ ℕ) (a : MvPolynomial S₁ K) (b : MvPolynomial S₂ K) :
    mvPolynomialCoeffInFirstVariables m (rename Sum.inl a * rename Sum.inr b) = coeff m a • b := by
  simp only [mvPolynomialCoeffInFirstVariables, LinearMap.comp_apply, AlgEquiv.toLinearMap_apply, LinearMap.restrictScalars_apply,
    lcoeff_apply, map_mul, sumAlgEquiv_rename_inl, sumAlgEquiv_rename_inr_eq_C']
  rw [mul_comm, coeff_C_mul, coeff_map, smul_eq_C_mul, mul_comm]
end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases
