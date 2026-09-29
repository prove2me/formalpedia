-- Prove2me | solution 1 for BookProof.NavierStokesFlow.FarisLavineLift.norm_vEx_sq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-09-11T10:28:50.970907+00:00
-- url     : https://prove2.me/submissions/da501e00-588e-47f1-964e-4b2fe2ebdeb1

import Mathlib
import Definitions.Def_ChapterNavierStokesFarisLavineLift
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.FarisLavineLift

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {d : ℕ} (c : ComparisonData F d)
variable {D : Submodule ℂ F}
variable {κ : Type*}

theorem solution : ‖vEx‖ ^ 2 = 2 := by
  norm_num [vEx, EuclideanSpace.norm_eq]
