-- Prove2me | solution 1 for Eden.exteriorOperator_comp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:18.252273+00:00
-- url     : https://prove2.me/submissions/0f6c2371-ff29-4a14-bb27-e5175ad4ae13

import Definitions.Def_Eden_ExteriorSingularValues
import Definitions.Def_Eden_Uniqueness
import Definitions.Def_Eden_ExteriorCocycle

set_option autoImplicit true
noncomputable section
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (A B : PhaseSpace →ₗ[ℝ] PhaseSpace) :
    exteriorOperator k (A ∘ₗ B) = (exteriorOperator k A).comp (exteriorOperator k B) := by
  apply ContinuousLinearMap.ext
  intro v
  exact congrArg (fun f : ExteriorSpace k →ₗ[ℝ] ExteriorSpace k => f v)
    (exteriorPower.map_comp B A)
end Eden
