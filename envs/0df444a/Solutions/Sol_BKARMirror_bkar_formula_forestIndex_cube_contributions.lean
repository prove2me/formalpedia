-- Prove2me | solution 1 for BKARMirror.bkar_formula_forestIndex_cube_contributions
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T10:40:09.251638+00:00
-- url     : https://prove2.me/submissions/11676ed6-546c-4a9b-af6e-edb86c5427ef

import Definitions.Def_BKAR
import Definitions.Def_Audit_ForestFormula_SolutionBasic
import Definitions.Def_Audit_ForestFormula_Solution
import Theorems.Thm_BKARMirror_oneConfig_bridge
import Theorems.Thm_BKARMirror_sum_bridge
import Theorems.Thm_BKAR_bkar_formula_forestIndex_cube_contributions


set_option autoImplicit false
noncomputable section
open MeasureTheory
open BKARMirror
variable {V : Type*} [Fintype V] [DecidableEq V]
namespace BKARMirror
theorem _root_.solution (ρ : (Edge V → ℝ) → ℝ)
    (hρ : ContDiffHyp ρ) :
    ρ (fun _ => 1) = ∑ J : ForestIndex V, cubeContribution J ρ :=
  calc ρ (fun _ => 1)
      = ρ BKAR.oneConfig := by rw [oneConfig_bridge]
    _ = ∑ I : BKAR.ForestIndex V, I.cubeContribution ρ :=
        BKAR.bkar_formula_forestIndex_cube_contributions ρ hρ
    _ = ∑ J : ForestIndex V, cubeContribution J ρ := (sum_bridge ρ hρ).symm
end BKARMirror
