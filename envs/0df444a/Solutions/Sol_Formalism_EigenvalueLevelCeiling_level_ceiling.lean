-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.level_ceiling
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:40:38.57121+00:00
-- url     : https://prove2.me/submissions/ef65e43e-143a-4ade-bcac-7bea7ef16d09

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
theorem _root_.solution : LevelCeil := by
  intro ρ T DL Dk g hρ hDL hTD hg
  have hDk : 0 ≤ Dk := le_trans (mul_nonneg (Nat.cast_nonneg T) hDL) hTD
  have hg1 : 0 < g - 1 := by linarith
  have hx : (T : ℝ) * (DL / (g - 1) + 1) ≤ (T : ℝ) + 1 := by
    have e1 : (T : ℝ) * (DL / (g - 1) + 1) = (T : ℝ) * DL / (g - 1) + T := by ring
    have e2 : (T : ℝ) * DL / (g - 1) ≤ 1 := by
      first
        | (rw [div_le_one hg1]; linarith)
        | (rw [div_le_one₀ hg1]; linarith)
        | (rw [div_le_iff₀ hg1]; linarith)
    linarith
  rw [Int.ceil_le]
  push_cast
  exact mul_le_mul_of_nonneg_left hx (by exact_mod_cast hρ)
end Formalism.EigenvalueLevelCeiling
