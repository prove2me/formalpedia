-- Prove2me | solution 1 for BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T23:07:20.030006+00:00
-- url     : https://prove2.me/submissions/b77667bd-5804-4db8-97cb-2ad28134109f
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

-- Generated from ChapterNavierStokesCarleman.lean — solution of BookProof.NavierStokesFlow.Carleman.halfLineFull_hasZeroDeficiencyOn
import Mathlib
import Definitions.Def_ChapterNavierStokesCarleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_tridiag_hasZeroDeficiencyOn_of_carleman
import Theorems.Thm_BookProof_NavierStokesFlow_Carleman_halfLineFullData_hamiltonian
import Definitions.Def_ChapterNavierStokesDeficiency
import Definitions.Def_ChapterNavierStokesFlow
import Definitions.Def_ChapterNavierStokesFullEsa
import Definitions.Def_ChapterNavierStokesAffineFiberEsa
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.Carleman



open scoped ENNReal



open LpNat DiagonalEsa FullEsa

set_option maxHeartbeats 1000000 in
theorem solution (c : Fin 15 → ℕ → ℝ) (nu : ℝ)
    (hcar : ¬ Summable fun n => 1 / ‖nsCoupling (halfLineSymbol c nu) n‖) :
    HasZeroDeficiencyOn (halfLineFullData c nu).D (halfLineFullData c nu).hamiltonian := by

  rw [halfLineFullData_hamiltonian]
  exact tridiag_hasZeroDeficiencyOn_of_carleman _ hcar
