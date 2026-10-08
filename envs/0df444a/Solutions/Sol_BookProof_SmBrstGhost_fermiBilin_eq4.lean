-- Prove2me | solution 1 for BookProof.SmBrstGhost.fermiBilin_eq4
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:57:04.435076+00:00
-- url     : https://prove2.me/submissions/7c46daad-bb0c-49ea-b0bc-527ad8ed63d3

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.fermiBilin_eq4
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (M : Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin M : Module.End ℂ (FermiFock N))
      = ∑ i : Fin N, ∑ j : Fin N, M i j • (creat i * annih j) := rfl
