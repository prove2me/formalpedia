-- Prove2me | solution 2 for CohnElkies.norm_gamma_imaginary_sq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:01:57.981625+00:00
-- url     : https://prove2.me/submissions/bd5bd8f9-cd2a-4a3c-a224-b33552f13c1a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped FourierTransform Interval RealInnerProductSpace Topology


theorem solution {x : ℝ} (hx : x ≠ 0) :
    ‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2 =
      Real.pi / (x * Real.sinh (Real.pi * x)) := by
  have hz : Complex.I * (x : ℂ) ≠ 0 := mul_ne_zero Complex.I_ne_zero (by exact_mod_cast hx)
  have hrefl := Complex.Gamma_mul_Gamma_one_sub (Complex.I * (x : ℂ))
  have hsin : Complex.sin ((Real.pi : ℂ) * (Complex.I * (x : ℂ))) =
      (Real.sinh (Real.pi * x) : ℂ) * Complex.I := by
    rw [show (Real.pi : ℂ) * (Complex.I * (x : ℂ)) = ((Real.pi * x : ℝ) : ℂ) * Complex.I by
      push_cast; ring, Complex.sin_mul_I, Complex.ofReal_sinh]
  have hone : 1 - Complex.I * (x : ℂ) = -(Complex.I * (x : ℂ)) + 1 := by ring
  rw [hone, Complex.Gamma_add_one _ (neg_ne_zero.2 hz), hsin] at hrefl
  have hconj : -(Complex.I * (x : ℂ)) = (starRingEnd ℂ) (Complex.I * (x : ℂ)) := by simp
  rw [hconj, Complex.Gamma_conj] at hrefl
  have hsh : Real.sinh (Real.pi * x) ≠ 0 := by
    intro h; rw [Real.sinh_eq_zero] at h
    rcases mul_eq_zero.1 h with h | h
    · exact Real.pi_ne_zero h
    · exact hx h
  have hcz : (starRingEnd ℂ) (Complex.I * (x : ℂ)) ≠ 0 := by simpa using hz
  apply Complex.ofReal_injective
  have hn : ((‖Complex.Gamma (Complex.I * (x : ℂ))‖ ^ 2 : ℝ) : ℂ) =
      Complex.Gamma (Complex.I * (x : ℂ)) * (starRingEnd ℂ) (Complex.Gamma (Complex.I * (x : ℂ))) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [hn]
  calc Complex.Gamma (Complex.I * (x : ℂ)) * (starRingEnd ℂ) (Complex.Gamma (Complex.I * (x : ℂ)))
      = (Complex.Gamma (Complex.I * (x : ℂ)) * ((starRingEnd ℂ) (Complex.I * (x : ℂ)) *
          (starRingEnd ℂ) (Complex.Gamma (Complex.I * (x : ℂ))))) /
          (starRingEnd ℂ) (Complex.I * (x : ℂ)) := by field_simp
    _ = (Real.pi : ℂ) / ((Real.sinh (Real.pi * x) : ℂ) * Complex.I) /
          (starRingEnd ℂ) (Complex.I * (x : ℂ)) := by rw [hrefl]
    _ = ((Real.pi / (x * Real.sinh (Real.pi * x)) : ℝ) : ℂ) := by
        rw [Complex.ofReal_div, Complex.ofReal_mul, div_div]
        congr 1
        simp only [map_mul, Complex.conj_I, Complex.conj_ofReal]
        linear_combination (-(Real.sinh (Real.pi * x) : ℂ) * (x : ℂ)) * Complex.I_sq

