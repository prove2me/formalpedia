-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.affF_antisymm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T08:38:48.404335+00:00
-- url     : https://prove2.me/submissions/5acf7171-8893-41e8-80ce-8660666a61ea

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.affF_antisymm
import Mathlib
import Definitions.Def_ChapterQuantumGravityBrstCharge
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
theorem solution (a b c : Fin 19) : affF a b c = -affF b a c := by

  simp only [affF, affEps]
  by_cases h : c = 1
  · simp only [h, if_true]
    split_ifs <;> simp_all
  · simp only [h, if_false, neg_zero]
