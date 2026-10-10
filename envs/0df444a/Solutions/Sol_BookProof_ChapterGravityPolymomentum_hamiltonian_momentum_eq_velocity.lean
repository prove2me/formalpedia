-- Prove2me | solution 1 for BookProof.ChapterGravityPolymomentum.hamiltonian_momentum_eq_velocity
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T14:27:23.630988+00:00
-- url     : https://prove2.me/submissions/e54ca48e-a3b4-4fe0-a712-f3cc62722d1d

-- Generated from ChapterGravityPolymomentum.lean — solution of BookProof.ChapterGravityPolymomentum.hamiltonian_momentum_eq_velocity
import Mathlib
import Definitions.Def_ChapterGravityPolymomentum
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_contract_smul_left
import Theorems.Thm_BookProof_ChapterGravityPolymomentum_contract_smul_right
import Definitions.Def_ChapterGravityProjector
open BookProof.ChapterGravityPolymomentum




open Matrix
open scoped BigOperators
open BookProof.ChapterGravityProjector

variable {e T : ℝ} {S Tc : Matrix (Fin 4) (Fin 4) ℝ} {u v : Fin 4 → ℝ}

set_option maxHeartbeats 1000000 in
theorem solution (he : e ≠ 0) (Scal E : Matrix (Fin 4) (Fin 4) ℝ)
    (P trE R : ℝ) (hS : Scal = (2 * e) • S) (hP : P = -4 * e * T) :
    (1 / (16 * e)) * contract Scal Scal - (1 / (24 * e)) * P ^ 2
        + (1 / 2) * contract Scal E + (1 / 3) * P * trE - e * R
      = e * ((1 / 4) * contract S S - (2 / 3) * T ^ 2 + contract S E
        - (4 / 3) * T * trE - R) := by

  subst hS hP
  rw [contract_smul_left, contract_smul_right, contract_smul_left]
  field_simp
  ring
