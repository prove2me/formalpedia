-- Prove2me | solution 1 for Formalism.REAL.lie_operators_gl_relations
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T13:37:38.192325+00:00
-- url     : https://prove2.me/submissions/887ad4dc-dbce-48e8-b31c-40f46c6ea2c5

import Definitions.Def_Formalism_RealPlaceAnalysis_SmoothVectorGrowthBound
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_MemUnitaryGroupIffMulConjTranspose
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexificationHolds
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_KoszulLowersPower
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ModularCharacterEqOneOnExpHermitian
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CasComm
import Definitions.Def_Development_AutomorphicArithmetic_IntegralCasts_CapelliIdentities_SmoothOnGroupSum
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_IntegrableComplexContinuousBoundedSupport
import Theorems.Thm_Formalism_REAL_quotient_mk_sub
import Theorems.Thm_Formalism_REAL_lie_operator_quotient_mk
import Theorems.Thm_Formalism_REAL_complex_parts_mem_lie_algebra_holds
import Theorems.Thm_Formalism_REAL_eabGl_of
import Theorems.Thm_Formalism_REAL_rdBracket_of
import Theorems.Thm_Formalism_REAL_rdSmooth_of
import Theorems.Thm_Formalism_REAL_right_derivative_extends
import Theorems.Thm_Formalism_REAL_right_derivative_linear


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix Filter Topology
open scoped ContDiff ENNReal
set_option linter.unusedSimpArgs false
noncomputable section
open Formalism Formalism.REAL
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {n : ℕ} (ε : Fin n → Bool)
variable {ε}
variable (ε)
variable {ε}
namespace Formalism.REAL
theorem _root_.solution : GlRel (lieOperatorQuotient ε) := by
  intro a b c d
  apply Submodule.linearMap_qext
  refine LinearMap.ext fun u => ?_
  have hGl := fun g (hg : inUJ ε g) => eabGl_of complex_parts_mem_lie_algebra_holds right_derivative_linear
    (rdBracket_of right_derivative_extends (rdSmooth_of right_derivative_extends)) (rdSmooth_of right_derivative_extends) n ε u a b c d g
    u.2 hg
  simp only [LinearMap.comp_apply, Submodule.mkQ_apply, LinearMap.sub_apply, Module.End.mul_apply]
  change lieOperatorQuotient ε a b (lieOperatorQuotient ε c d (quotientMkAlt u)) - lieOperatorQuotient ε c d (lieOperatorQuotient ε a b (quotientMkAlt u)) =
    (if b = c then lieOperatorQuotient ε a d else 0) (quotientMkAlt u) - (if d = a then lieOperatorQuotient ε c b else 0) (quotientMkAlt u)
  simp only [lie_operator_quotient_mk]
  by_cases h1 : b = c <;> by_cases h2 : d = a <;>
    simp only [h1, h2, if_true, if_false, LinearMap.zero_apply, lie_operator_quotient_mk] at hGl ⊢
  · rw [← quotient_mk_sub, ← quotient_mk_sub, quotient_mk_eq_iff]
    intro g hg; have := hGl g hg
    simp only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_mk, Pi.sub_apply,
      Pi.zero_apply, sub_zero, zero_sub, Submodule.coe_neg, Pi.neg_apply] at this ⊢
    linear_combination this
  · rw [← quotient_mk_sub, ← quotient_mk_zero, ← quotient_mk_sub, quotient_mk_eq_iff]
    intro g hg; have := hGl g hg
    simp only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_mk, Pi.sub_apply,
      Pi.zero_apply, sub_zero, zero_sub, Submodule.coe_neg, Pi.neg_apply] at this ⊢
    linear_combination this
  · rw [← quotient_mk_sub, ← quotient_mk_zero, ← quotient_mk_sub, quotient_mk_eq_iff]
    intro g hg; have := hGl g hg
    simp only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_mk, Pi.sub_apply,
      Pi.zero_apply, sub_zero, zero_sub, Submodule.coe_neg, Pi.neg_apply] at this ⊢
    linear_combination this
  · rw [← quotient_mk_sub, sub_zero, ← quotient_mk_zero, quotient_mk_eq_iff]
    intro g hg; have := hGl g hg
    simp only [Submodule.coe_sub, Submodule.coe_zero, Submodule.coe_mk, Pi.sub_apply,
      Pi.zero_apply, sub_zero, zero_sub, Submodule.coe_neg, Pi.neg_apply] at this ⊢
    linear_combination this
end Formalism.REAL
