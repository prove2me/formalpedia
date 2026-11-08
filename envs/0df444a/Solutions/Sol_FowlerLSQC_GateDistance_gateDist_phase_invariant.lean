-- Prove2me | solution 1 for FowlerLSQC.GateDistance.gateDist_phase_invariant
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T15:16:53.281265+00:00
-- url     : https://prove2.me/submissions/5d0e284d-fc56-43b7-9430-de0a38e0c3ae

import Mathlib
import Definitions.Def_FowlerLSQC_GateDistance_gateDist
import Definitions.Def_FowlerLSQC_GateDistance_phaseShift

open scoped Matrix

open FowlerLSQC.GateDistance in
theorem solution {m : ℕ} (hm : 0 < m) (α β : ℝ)
    (U V : Matrix.unitaryGroup (Fin m) ℂ) :
    gateDist (phaseShift α U) (phaseShift β V) = gateDist U V := by
  have h : ‖((phaseShift α U : Matrix (Fin m) (Fin m) ℂ)ᴴ *
      (phaseShift β V : Matrix (Fin m) (Fin m) ℂ)).trace‖ =
      ‖((U : Matrix (Fin m) (Fin m) ℂ)ᴴ * (V : Matrix (Fin m) (Fin m) ℂ)).trace‖ := by
    rw [coe_phaseShift, coe_phaseShift, Matrix.conjTranspose_smul, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.trace_smul, Matrix.trace_smul, smul_eq_mul, smul_eq_mul,
      norm_mul, norm_mul, norm_star, Complex.norm_exp_ofReal_mul_I,
      Complex.norm_exp_ofReal_mul_I, one_mul, one_mul]
  unfold gateDist
  rw [h]
