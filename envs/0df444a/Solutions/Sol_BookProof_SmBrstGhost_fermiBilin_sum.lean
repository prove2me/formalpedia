-- Prove2me | solution 1 for BookProof.SmBrstGhost.fermiBilin_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T13:34:40.854719+00:00
-- url     : https://prove2.me/submissions/dbc4dd8a-d7d5-4ecc-b046-abecfb0b957b

-- Generated from ChapterSmBrstGhost.lean — solution of BookProof.SmBrstGhost.fermiBilin_sum
import Mathlib
import Definitions.Def_ChapterSmBrstGhost
import Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_eq4
import Theorems.Thm_BookProof_SmBrstGhost_fermiBilin_add_prime
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
theorem solution {ι : Type*} (s : Finset ι) (M : ι → Matrix (Fin N) (Fin N) ℂ) :
    (fermiBilin (∑ t ∈ s, M t) : Module.End ℂ (FermiFock N))
      = ∑ t ∈ s, fermiBilin (M t) := by

  classical
  induction s using Finset.induction with
  | empty =>
      rw [Finset.sum_empty, Finset.sum_empty, fermiBilin_eq4]
      refine Finset.sum_eq_zero fun i _ => Finset.sum_eq_zero fun j _ => ?_
      simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha, ← ih]
      exact fermiBilin_add_prime (M a) (∑ t ∈ s, M t)
