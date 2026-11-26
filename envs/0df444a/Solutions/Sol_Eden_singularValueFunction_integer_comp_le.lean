-- Prove2me | solution 1 for Eden.singularValueFunction_integer_comp_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:52:33.380606+00:00
-- url     : https://prove2.me/submissions/daca2cdd-8005-41cf-a275-f3affb2db7e3

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle
import Theorems.Thm_Eden_exteriorOperator_comp
import Theorems.Thm_Eden_norm_exteriorOperator_eq_singularValueFunction


set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution {k : ℕ} (hk : k ≤ 5)
    (A B : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    singularValueFunction (A ∘ₗ B) k ≤ singularValueFunction A k * singularValueFunction B k := by
  rw [← norm_exteriorOperator_eq_singularValueFunction hk,
    ← norm_exteriorOperator_eq_singularValueFunction hk A,
    ← norm_exteriorOperator_eq_singularValueFunction hk B, exteriorOperator_comp]
  exact ContinuousLinearMap.opNorm_comp_le _ _
end Eden
