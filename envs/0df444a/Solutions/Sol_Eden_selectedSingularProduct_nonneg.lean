-- Prove2me | solution 1 for Eden.selectedSingularProduct_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:35:26.118961+00:00
-- url     : https://prove2.me/submissions/11e8fc73-7311-419d-ab65-ecada6e491e5

import Definitions.Def_Eden_ExteriorOperatorNorm
import Definitions.Def_Eden_ExteriorGram

set_option autoImplicit true
noncomputable section
open scoped RealInnerProductSpace
open Eden
namespace Eden
theorem _root_.solution (k : ℕ) (A : PhaseSpace →ₗ[ℝ] PhaseSpace)
    (s : ExteriorIndex k) : 0 ≤ selectedSingularProduct k A s :=
  Finset.prod_nonneg (fun _i _ => A.singularValues_nonneg _)
end Eden
