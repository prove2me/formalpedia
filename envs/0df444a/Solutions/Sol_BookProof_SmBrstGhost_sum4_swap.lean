-- Prove2me | solution 1 for BookProof.SmBrstGhost.sum4_swap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:55:52.516983+00:00
-- url     : https://prove2.me/submissions/06b369f2-8399-4e23-9278-55a2fd27e61d

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.sum4_swap
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterSmCarAlgebra
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {N : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (F : Fin N → Fin N → Fin N → Fin N → Module.End ℂ (FermiFock N)) :
    ∑ k : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N, F i j k l
      = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, F i j k l := by

  calc ∑ k : Fin N, ∑ l : Fin N, ∑ i : Fin N, ∑ j : Fin N, F i j k l
      = ∑ q : Fin N × Fin N, ∑ p : Fin N × Fin N, F p.1 p.2 q.1 q.2 := by
        simp [Fintype.sum_prod_type]
    _ = ∑ p : Fin N × Fin N, ∑ q : Fin N × Fin N, F p.1 p.2 q.1 q.2 := Finset.sum_comm
    _ = ∑ i : Fin N, ∑ j : Fin N, ∑ k : Fin N, ∑ l : Fin N, F i j k l := by
        simp [Fintype.sum_prod_type]
