-- Prove2me | solution 1 for BookProof.QuantumGravityBrstCharge.linGen_smul_sum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:42:50.569477+00:00
-- url     : https://prove2.me/submissions/967affea-6649-494d-b7fd-c1402494ef6d

-- Generated from ChapterQuantumGravityBrstCharge.lean — solution of BookProof.QuantumGravityBrstCharge.linGen_smul_sum
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

set_option maxHeartbeats 1000000 in
theorem solution {n : ℕ} (c : Fin n → ℝ) (M : Fin n → Matrix (Fin d) (Fin d) ℝ) :
    linGen (∑ e, c e • M e) = ∑ e, c e • linGen (M e) := by

  rw [linGen, map_sum]
  exact Finset.sum_congr rfl fun e _ => map_smul linGenLM (c e) (M e)
