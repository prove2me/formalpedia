-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ceiling_shift
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T16:27:59.754683+00:00
-- url     : https://prove2.me/submissions/9b71cb17-3dd1-494b-b63b-4740af7bc4b1

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
theorem _root_.solution : CeilShift := by
  intro ρ vS T ν β hρ
  have hρ' : (ρ : ℝ) ≠ 0 := by exact_mod_cast hρ.ne'
  have hq : (ρ : ℝ) * ((vS : ℝ) / (ρ : ℝ)) = vS := by
    first
      | field_simp
      | exact mul_div_cancel₀ _ hρ'
  have e : (ρ : ℝ) * ((T : ℝ) * (ν - (vS : ℝ) / (ρ : ℝ) + β)) =
      (ρ : ℝ) * ((T : ℝ) * (ν + β)) - (((T : ℤ) * vS : ℤ) : ℝ) := by
    push_cast
    linear_combination (-(T : ℝ)) * hq
  rw [e]
  first
    | rw [Int.ceil_sub_intCast]
    | rw [Int.ceil_sub_int]
    | simp
end Formalism.EigenvalueLevelCeiling
