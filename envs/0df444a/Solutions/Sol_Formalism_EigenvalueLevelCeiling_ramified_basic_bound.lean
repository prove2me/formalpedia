-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.ramified_basic_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:56:22.814096+00:00
-- url     : https://prove2.me/submissions/c27ba9d2-7787-4356-985a-152ebf26ff3d

import Mathlib
import Definitions.Def_Formalism_MirabolicMackeyTheory_StatementT
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_BoundsChain
import Definitions.Def_Formalism_LogFactorialIndices_SignedSubspaceIndex_LogProductFormula
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_RamBasic
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_plc_prime
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_one_le_ramw
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_plc_conjPl
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_ramw_conjPl

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
theorem _root_.solution : RamBasic := by
  unfold RamBasic
  intro K _ _ _ w
  refine ⟨plc_prime w, one_le_ramw w, plc_conjPl w, ramw_conjPl w, ?_⟩
  have h1 : (1:ℝ) ≤ (ramw w : ℝ) := by exact_mod_cast one_le_ramw w
  have hp : (0:ℝ) < (plc w : ℝ) := by exact_mod_cast (plc_prime w).pos
  unfold ellw
  rw [div_pow, Real.sq_sqrt (by linarith)]
  have h2 : (ramw w : ℝ) ≠ 0 := by linarith
  have h3 : (plc w : ℝ) ≠ 0 := hp.ne'
  first
    | (field_simp; ring)
    | field_simp
end Formalism.EigenvalueLevelCeiling
