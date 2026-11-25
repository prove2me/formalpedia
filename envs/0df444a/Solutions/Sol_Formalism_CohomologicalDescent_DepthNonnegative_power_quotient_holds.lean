-- Prove2me | solution 1 for Formalism.CohomologicalDescent.DepthNonnegative.power_quotient_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:15:29.790084+00:00
-- url     : https://prove2.me/submissions/495ec943-74f4-40fe-a2d0-469388e9ac3c

import Definitions.Def_Formalism_PieriBlockIdeals_BlockIdealBound5Derived
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_ProdInitialMinorsMemDetSpan
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_UnitNormBounds
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_JointCorollaryFiveBound
import Definitions.Def_Formalism_GradedWeylDivisibility_FinalC
import Definitions.Def_Formalism_GradedWeylDivisibility_FockSpaceTableaux_LDbasisLemmas
import Definitions.Def_Formalism_RankGapBounds_RankGapProofs_FormsTensorLocalization
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_RegularCuspidalTrace
import Definitions.Def_Formalism_PieriBlockIdeals_PieriColumnMinors_DepthNonnegative
import Theorems.Thm_Formalism_GradedWeylDivisibility_rowDivL_apply
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
attribute [local simp] Formalism.GradedWeylDivisibility.rowDivL_apply



set_option autoImplicit false
noncomputable section
open TensorProduct MvPolynomial
open Formalism Formalism.CohomologicalDescent Formalism.CohomologicalDescent.DepthNonnegative
open Formalism.UG Formalism.RankGapBounds.FormsTensorLocalization Formalism.GradedWeylDivisibility Formalism.CohomologicalDescent.LD Formalism.CohomologicalDescent.UnitNormBounds
open CategoryTheory CategoryTheory.Limits
namespace Formalism.CohomologicalDescent.DepthNonnegative
theorem _root_.solution : PowQuotient := by
  intro O _ A _ _ V _ _ _ _ ϖ a
  have hker : scaleSub A V ϖ ≤ LinearMap.ker
      (((scaleSub A V (ϖ ^ (a + 1))).comap (scaleSub A V (ϖ ^ a)).subtype).mkQ ∘ₗ
        mulOntoScaledSubmodule A V (ϖ ^ a)) := by
    rintro _ ⟨y, rfl⟩
    rw [LinearMap.mem_ker, LinearMap.comp_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.mem_comap]
    exact ⟨y, by
      show ϖ ^ a • ϖ • y = ϖ ^ (a + 1) • y
      rw [pow_succ, mul_smul]⟩
  refine ⟨(scaleSub A V ϖ).liftQ _ hker, ?_, ?_, ?_⟩
  · intro v
    rfl
  · intro z
    obtain ⟨⟨x, y, rfl⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    exact ⟨Submodule.Quotient.mk y, rfl⟩
  · intro hreg
    have hpow : ∀ (b : ℕ) (v : V), ϖ ^ b • v = 0 → v = 0 := by
      intro b
      induction b with
      | zero => intro v hv; simpa using hv
      | succ b ih =>
        intro v hv
        rw [pow_succ, mul_smul] at hv
        exact hreg v (ih _ hv)
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    obtain ⟨v, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    have h1 : (Submodule.Quotient.mk (⟨ϖ ^ a • v, v, rfl⟩ : scaleSub A V (ϖ ^ a)) :
        scaleSub A V (ϖ ^ a) ⧸ (scaleSub A V (ϖ ^ (a + 1))).comap (scaleSub A V (ϖ ^ a)).subtype) = 0 := hz
    rw [Submodule.Quotient.mk_eq_zero, Submodule.mem_comap] at h1
    obtain ⟨y, hy⟩ := h1
    rw [Submodule.Quotient.mk_eq_zero]
    refine ⟨y, ?_⟩
    have h2 : ϖ ^ a • (v - ϖ • y) = 0 := by
      have h3 : ϖ ^ a • v = ϖ ^ (a + 1) • y := hy
      rw [smul_sub, h3, pow_succ, mul_smul, sub_self]
    exact sub_eq_zero.mp (hpow a _ h2)
end Formalism.CohomologicalDescent.DepthNonnegative
