-- Prove2me | solution 1 for Eden.selectedSingularProduct_eq_prod
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:46:07.718595+00:00
-- url     : https://prove2.me/submissions/6609c82a-a662-4183-87a3-c5b3d2567a92

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram
import Theorems.Thm_Eden_exteriorFactor_eq_prod


set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : selectedSingularProduct k A s = ∏ j ∈ s.val, A.singularValues j := by
  change exteriorFactor k (WithLp.toLp 2 (fun i : Fin 5 => A.singularValues i)) s = _
  exact exteriorFactor_eq_prod k _ s
end Eden
