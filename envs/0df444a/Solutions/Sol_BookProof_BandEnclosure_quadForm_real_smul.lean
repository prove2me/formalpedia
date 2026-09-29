-- Prove2me | solution 1 for BookProof.BandEnclosure.quadForm_real_smul
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:23:22.49345+00:00
-- url     : https://prove2.me/submissions/ce521f9c-958a-4268-a37e-417f69d46c8c

import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.LinearAlgebra.Complex.Module
import Mathlib.Tactic.Ring
set_option autoImplicit false
variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

theorem solution {D : Submodule ℂ F} (H : D →ₗ[ℂ] F) (c : ℝ) (x : D) :
    (inner ℂ (((c : ℂ) • x : D) : F) (H ((c : ℂ) • x)) : ℂ).re =
      c ^ 2 * (inner ℂ (x : F) (H x) : ℂ).re := by
  simp only [map_smul, Submodule.coe_smul, inner_smul_left, inner_smul_right,
    Complex.conj_ofReal, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, mul_zero, sub_zero]
  ring
#print axioms solution
