-- Prove2me | solution 1 for BookProof.SmBrstGhost.sum_rotate4
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:55:49.69257+00:00
-- url     : https://prove2.me/submissions/f76f96c4-31c2-44f5-9f31-a90352c74e7a

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.sum_rotate4
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsSU3
open BookProof.SmBrstGhost




open BookProof.SmCar BookProof.BRSTNilpotent BookProof.YangMillsSU3

noncomputable section

variable {m : ℕ}
variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {M : Type*} [AddCommMonoid M] {n : ℕ} (F : Fin n → Fin n → Fin n → Fin n → M) :
    ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, ∑ a : Fin n, F a d g h
      = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, F a d g h := by

  calc ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, ∑ a : Fin n, F a d g h
      = ∑ d : Fin n, ∑ g : Fin n, ∑ a : Fin n, ∑ h : Fin n, F a d g h :=
        Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun g _ => Finset.sum_comm
    _ = ∑ d : Fin n, ∑ a : Fin n, ∑ g : Fin n, ∑ h : Fin n, F a d g h :=
        Finset.sum_congr rfl fun d _ => Finset.sum_comm
    _ = ∑ a : Fin n, ∑ d : Fin n, ∑ g : Fin n, ∑ h : Fin n, F a d g h := Finset.sum_comm
