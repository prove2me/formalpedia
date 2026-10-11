-- Prove2me | solution 1 for BookProof.SmBrstGhost.fermiBilin_smul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:56:08.695283+00:00
-- url     : https://prove2.me/submissions/980addbe-3983-4ff9-845f-f701d1299772

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.fermiBilin_smul
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_eq4
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterNavierStokesFockSpace
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (c : ℂ) (M : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (c • M) : Module.End ℂ (FermiFock N)) = c • fermiBilin M := by

  rw [fermiBilin_eq4, fermiBilin_eq4, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [Matrix.smul_apply, smul_eq_mul, mul_smul]
