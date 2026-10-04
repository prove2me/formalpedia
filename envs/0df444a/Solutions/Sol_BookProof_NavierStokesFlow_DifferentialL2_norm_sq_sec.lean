-- Prove2me | solution 1 for BookProof.NavierStokesFlow.DifferentialL2.norm_sq_sec
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-03T10:06:51.662922+00:00
-- url     : https://prove2.me/submissions/bde10efe-b1fe-47ba-859c-add12ad4fb3d

import Mathlib
import Definitions.Def_ChapterHermiteProductBasis
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesIkebeKato
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterNavierStokesThreeComponent
import Definitions.Def_ChapterNavierStokesCanonicalVector
import Definitions.Def_ChapterNavierStokesLagrangianEsa
import Definitions.Def_ChapterNavierStokesDifferentialL2
import Definitions.Def_ChapterHermiteProductCore

set_option autoImplicit false

open BookProof.HermiteProductCore BookProof.NavierStokesFlow.DifferentialL2 in
theorem solution {d : ℕ} (i : Fin d) (x : Vd d) (t : ℝ) :
    ‖sec i x t‖ ^ 2 = (∑ j ∈ Finset.univ.erase i, (x j) ^ 2) + t ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, ← Finset.add_sum_erase _ _ (Finset.mem_univ i), add_comm]
  congr 1
  · apply Finset.sum_congr rfl
    intro j hj
    have hji : j ≠ i := Finset.ne_of_mem_erase hj
    simp [sec, Function.update_of_ne hji]
  · simp [sec]
