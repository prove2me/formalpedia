-- Prove2me | solution 1 for BookProof.FockOneParticleGap.fock_gap_of_one_particle_gap
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-12T23:36:30.984354+00:00
-- url     : https://prove2.me/submissions/56afdf0e-147a-4825-8497-09120c6d7516

-- Generated from ChapterFockOneParticleGap.lean — solution of BookProof.FockOneParticleGap.fock_gap_of_one_particle_gap
import Mathlib
import Definitions.Def_ChapterFockOneParticleGap
import Theorems.Thm_BookProof_FockOneParticleGap_dGamma_diagCol_vac
import Theorems.Thm_BookProof_FockOneParticleGap_fock_gap_quadForm
import Theorems.Thm_BookProof_FockOneParticleGap_inner_vac
import Theorems.Thm_BookProof_FockSecondQuantization_coe_dGammaOp
import Theorems.Thm_BookProof_FockSecondQuantization_coe_fockEquiv_symm
open BookProof.FockOneParticleGap













noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

set_option maxHeartbeats 1000000 in
theorem solution {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu)
    (he : ∀ k, mu ≤ e k) :
    dGammaOp (diagCol e) (fockEquiv vac) = 0 ∧
      ∀ x : lpFiniteModes Conf, (inner ℂ (toLp vac) ((x : Fock)) : ℂ) = 0 →
        mu * ‖(x : Fock)‖ ^ 2 ≤ quadForm (dGammaOp (diagCol e)) x := by

  constructor
  · rw [coe_dGammaOp, LinearEquiv.symm_apply_apply, dGamma_diagCol_vac]
    exact map_zero toLpL
  · intro x hx
    rw [quadForm, coe_dGammaOp, coe_fockEquiv_symm x]
    rw [coe_fockEquiv_symm x] at hx
    exact fock_gap_quadForm hmu he (by rwa [inner_vac] at hx)
