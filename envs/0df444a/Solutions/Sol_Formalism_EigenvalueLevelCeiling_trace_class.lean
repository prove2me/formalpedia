-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.trace_class
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T16:37:20.520075+00:00
-- url     : https://prove2.me/submissions/62c2c37d-ad10-4d16-9222-20e12c55719d

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField IsDedekindDomain
noncomputable section
open Formalism Formalism.EigenvalueLevelCeiling
open Formalism.DivisionValues
namespace Formalism.EigenvalueLevelCeiling
theorem _root_.solution : TraceClass := by
  intro R N Y Γ _ _ _ _ _ _ _ ρ lam θ hθ P
  refine ⟨fun γ' => ?_, ?_, fun N0 hρ hl hP => ?_⟩
  · rw [map_sum, Finset.smul_sum]
    simp only [map_smul]
    apply Fintype.sum_equiv (Equiv.mulLeft γ')
    intro γ
    have hl1 : lam γ'⁻¹ * lam γ' = 1 := by
      first
        | rw [← map_mul, inv_mul_cancel, map_one]
        | rw [← map_mul, mul_left_inv, map_one]
        | simp [← map_mul]
    simp only [Equiv.coe_mulLeft, map_mul, smul_smul]
    rw [← mul_assoc, hl1, one_mul]
    first
      | rfl
      | simp [Module.End.mul_apply]
  · rw [map_sum]
    simp only [map_smul]
    rw [Finset.sum_congr rfl (fun γ _ => (hθ γ P).symm), Finset.sum_const, Finset.card_univ]
    first
      | rw [Nat.cast_smul_eq_nsmul]
      | simp
  · exact AddSubgroup.sum_mem N0 (fun γ _ => hl γ _ (hρ γ P hP))
end Formalism.EigenvalueLevelCeiling
