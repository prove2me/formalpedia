-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.affF_jacobi
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:38:50.733003+00:00
-- url     : https://prove2.me/submissions/f7e83e84-ed60-4f49-9c2f-e68a739f4375

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.affF_jacobi
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
import Theorems.Thm_BookProof_QuantumGravityBrstCharge_affF_contract
import Definitions.Def_ChapterBRSTNilpotent
import Definitions.Def_ChapterYangMillsHermite
import Definitions.Def_ChapterQuantumGravity3DGauge
open BookProof.QuantumGravityBrstCharge




open MvPolynomial BookProof.BRSTNilpotent BookProof.YangMillsHermite
open BookProof.QuantumGravity3DGauge

noncomputable section

variable {R : Type*} [Ring R] [Algebra ℝ R] {n : ℕ}
variable {f : Fin n → Fin n → Fin n → ℝ} {G χ β : Fin n → R}
variable {d : ℕ}
variable {α : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (a b c h : Fin 19) :
    ∑ e, (affF a b e * affF e c h + affF b c e * affF e a h + affF c a e * affF e b h) = 0 := by

  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, affF_contract, affF_contract, affF_contract]
  by_cases hh : h = 1
  · subst hh
    simp only []
    by_cases ha0 : a = 0 <;> by_cases ha1 : a = 1 <;> by_cases hb0 : b = 0 <;>
      by_cases hb1 : b = 1 <;> by_cases hc0 : c = 0 <;> by_cases hc1 : c = 1 <;>
      simp_all [affEps]
  · simp [hh]
