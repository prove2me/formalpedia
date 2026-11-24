-- Prove2me | solution 1 for Formalism.HermitianLattices.GenusMassVolumes.real_gaussian_integral
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:41:47.516373+00:00
-- url     : https://prove2.me/submissions/fcf5c725-ff2c-447a-8dfb-40d9aa56f3ee

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_RankMulPowThreeHalvesLeFourthPower
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_CardUnitsZmodPrimeSq

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GenusMassVolumes
open Finset MeasureTheory
namespace Formalism.HermitianLattices.GenusMassVolumes
theorem _root_.solution : SW_real_gaussian := by
  intro M τ b hτ
  have hne : τ + 2 * (b : ℂ) ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  set β : ℂ := -(Real.pi * Complex.I * (τ + 2 * (b : ℂ))) with hβ
  have hre : 0 < β.re := by
    simp [hβ]
    exact mul_pos Real.pi_pos hτ
  have hint := GaussianFourier.integral_cexp_neg_mul_sq_norm
    (V := EuclideanSpace ℝ (Fin (2 * M))) hre
  have hcongr : (∫ x : EuclideanSpace ℝ (Fin (2 * M)),
        Complex.exp (Real.pi * Complex.I * τ * ((‖x‖ ^ 2 : ℝ) : ℂ)
          + 2 * Real.pi * Complex.I * b * ((‖x‖ ^ 2 : ℝ) : ℂ)))
      = ∫ x : EuclideanSpace ℝ (Fin (2 * M)), Complex.exp (-β * (‖x‖ : ℂ) ^ 2) := by
    congr 1
    ext x
    congr 1
    rw [hβ]
    push_cast
    ring
  rw [hcongr, hint]
  have hfin : ((Module.finrank ℝ (EuclideanSpace ℝ (Fin (2 * M))) : ℂ) / 2) = (M : ℂ) := by
    simp
  rw [hfin, Complex.cpow_natCast, ← mul_pow]
  congr 1
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [hβ]
  field_simp
  ring_nf
  simp
end Formalism.HermitianLattices.GenusMassVolumes
