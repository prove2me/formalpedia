-- Prove2me | solution 1 for BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-06T00:28:24.499414+00:00
-- url     : https://prove2.me/submissions/ece2ae6f-bdad-459e-8f9f-0dc9877f4a00

-- Generated from ChapterFockNumberPreservingGap.lean — solution of BookProof.FockNumberPreservingGap.fock_gap_of_number_preserving_op
import Mathlib
import Definitions.Def_ChapterFockNumberPreservingGap
import Theorems.Thm_BookProof_FockNumberPreservingGap_dGamma_vac
import Theorems.Thm_BookProof_FockNumberPreservingGap_fock_gap_of_number_preserving
import Theorems.Thm_BookProof_FockOneParticleGap_inner_vac
import Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
import Theorems.Thm_BookProof_FockSecondQuantization_coe_fockEquiv_symm
open BookProof.FockNumberPreservingGap



noncomputable section


open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.FarisLavine BookProof.NavierStokesFlow

set_option maxHeartbeats 1000000 in
theorem solution {col : ℕ → (ℕ →₀ ℂ)} {mu : ℝ} (hmu : 0 ≤ mu)
    (hgap : IsPosCol (shiftCol col mu)) :
    dGammaOp col (fockEquiv vac) = 0 ∧
      ∀ x : lpFiniteModes Conf, (inner ℂ (toLp vac) ((x : Fock)) : ℂ) = 0 →
        mu * ‖(x : Fock)‖ ^ 2 ≤ quadForm (dGammaOp col) x := by

  constructor
  · rw [coe_dGammaOp, LinearEquiv.symm_apply_apply, dGamma_vac]
    exact map_zero toLpL
  · intro x hx
    rw [quadForm, coe_dGammaOp, coe_fockEquiv_symm x]
    rw [coe_fockEquiv_symm x] at hx
    exact fock_gap_of_number_preserving hmu hgap (by rwa [inner_vac] at hx)
