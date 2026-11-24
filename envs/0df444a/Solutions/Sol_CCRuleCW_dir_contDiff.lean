-- Prove2me | solution 1 for CCRuleCW.dir_contDiff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T15:21:21.38309+00:00
-- url     : https://prove2.me/submissions/1ff25163-6b0e-474e-aed8-3d8126adf80c

import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_ExpIntertwine
import Definitions.Def_Formalism_PeriodIntegrals_UnitaryGroupMassFormula_ChainRuleSmooth_Curves

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Filter Topology
open scoped ComplexConjugate Nat ContDiff
noncomputable section
open CCRuleCW
open Formalism.FourierDecayAlt
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
namespace CCRuleCW
theorem _root_.solution (o : Bool × B.Mat k r) : ContDiff ℝ ∞ (dir o) := by
  rcases o with ⟨_ | _, X⟩
  · let L : B.Mat k r →ₗ[ℝ] B.Mat k r :=
      { toFun := fun g => g * X
        map_add' := fun a b => Matrix.add_mul a b X
        map_smul' := fun c a => Matrix.smul_mul c a X }
    exact (LinearMap.toContinuousLinearMap L).contDiff
  · let L : B.Mat k r →ₗ[ℝ] B.Mat k r :=
      { toFun := fun g => -(X * g)
        map_add' := fun a b => by simp only [Matrix.mul_add, neg_add]
        map_smul' := fun c a => by simp only [Matrix.mul_smul, smul_neg, RingHom.id_apply] }
    exact (LinearMap.toContinuousLinearMap L).contDiff
end CCRuleCW
