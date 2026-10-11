-- Prove2me | solution 1 for BookProof.SmGaugeConnection.conn_gauge_transform
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:10:39.20868+00:00
-- url     : https://prove2.me/submissions/2c45f34e-96c7-4798-a5a4-154829159594

-- Generated from ChapterSmGaugeConnection.lean — solution of BookProof.SmGaugeConnection.conn_gauge_transform
import Mathlib
import Definitions.Def_ChapterSmGaugeConnection
import Definitions.Def_ChapterYangMillsSU3
import Definitions.Def_ChapterCPTHamiltonian
import Definitions.Def_ChapterSmCarAlgebra
import Definitions.Def_ChapterSmDiracYukawa
import Definitions.Def_ChapterSmDiracSpinor
import Definitions.Def_ChapterFarisLavine
open BookProof.SmGaugeConnection




open Matrix Kronecker
open BookProof.YangMillsSU3 BookProof.ChapterCPTHamiltonian BookProof.SmCar
open BookProof.SmDiracYukawa BookProof.SmDiracSpinor BookProof.FarisLavine

noncomputable section

variable {N d : ℕ}

variable {N d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution {g : ℝ} {T : Fin d → Matrix (Fin N) (Fin N) ℂ}
    {A : Fin d → Fin 3 → ℝ} {U : Matrix (Fin N) (Fin N) ℂ} {R : Fin d → Fin d → ℝ}
    (hUT : ∀ a, U * T a * Uᴴ = ∑ b : Fin d, ((R a b : ℝ) : ℂ) • T b) (j : Fin 3) :
    U * conn g T A j * Uᴴ = conn g T (fun b i => ∑ a : Fin d, R a b * A a i) j := by

  have h1 : U * conn g T A j * Uᴴ
      = ∑ a : Fin d, ((g * A a j : ℝ) : ℂ) • (U * T a * Uᴴ) := by
    rw [conn, Matrix.mul_sum, Matrix.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by rw [Matrix.mul_smul, Matrix.smul_mul]
  rw [h1]
  simp only [hUT, Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm, conn]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  push_cast
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun a _ => by ring
