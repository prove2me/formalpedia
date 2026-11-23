-- Prove2me | solution 1 for Formalism.EigenvalueLevelCeiling.levelCeil_tower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T18:33:35.776277+00:00
-- url     : https://prove2.me/submissions/112262cc-8cff-412f-b557-54689a4841f6

import Definitions.Def_Formalism_MirabolicMackeyTheory_LocalConditionsWeighted
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicIsMackey
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_LocalConditionsGlobalForm
import Definitions.Def_Formalism_QuotientMetricDivisors_HermitianTwistDivisors_ValBasic
import Definitions.Def_Formalism_MirabolicMackeyTheory_MirabolicMackeyProofs_GlobalBoundRefinements
import Theorems.Thm_Formalism_EigenvalueLevelCeiling_level_ceiling

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
theorem _root_.solution (ρ1 ρ2 : ℤ) (T : ℕ) (DL Dk g : ℝ) (h1 : 0 ≤ ρ1) (h2 : 0 ≤ ρ2) (h3 : 0 ≤ DL)
    (h4 : (T : ℝ) * DL ≤ Dk) (h5 : 2 * Dk + 2 < g) :
    ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ ≤ (ρ1 * ρ2) * ((T : ℤ) + 1) := by
  calc ρ1 * ⌈(ρ2 : ℝ) * ((T : ℝ) * (DL / (g - 1) + 1))⌉ ≤ ρ1 * (ρ2 * ((T : ℤ) + 1)) :=
        mul_le_mul_of_nonneg_left (level_ceiling ρ2 T DL Dk g h2 h3 h4 h5) h1
    _ = (ρ1 * ρ2) * ((T : ℤ) + 1) := by ring
end Formalism.EigenvalueLevelCeiling
