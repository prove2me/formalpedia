-- Prove2me | solution 1 for BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le_prime
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:37:27.74282+00:00
-- url     : https://prove2.me/submissions/bf3cdd9b-c84d-433f-b44b-e65930df95e5

-- Generated from ChapterEnergyBandDecomposition.lean — solution of BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le'
import Mathlib
import Definitions.Def_ChapterEnergyBandDecomposition
open BookProof.EnergyBandDecomposition




open MeasureTheory

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

variable {X : Type*} {E : X → ℝ} {ε : ℝ} {k : ℤ} {x : X}

set_option maxHeartbeats 1000000 in
theorem solution {a : ℝ} (t c : ℝ) (z : ℂ) (h : |a - c| ≤ ε) :
    ‖Complex.exp (-(Complex.I * (t * a))) * z
        - Complex.exp (-(Complex.I * (t * c))) * z‖ ≤ |t| * ε * ‖z‖ := by

  have hrw : ∀ r : ℝ, Complex.exp (-(Complex.I * ((t : ℂ) * (r : ℂ))))
      = Complex.exp (Complex.I * ((-(t * r) : ℝ) : ℂ)) := by
    intro r
    congr 1
    push_cast
    ring
  set u : ℝ := -(t * a) with hu
  set w : ℝ := -(t * c) with hw
  have hfac : Complex.exp (Complex.I * (u : ℂ)) - Complex.exp (Complex.I * (w : ℂ))
      = Complex.exp (Complex.I * (w : ℂ)) * (Complex.exp (Complex.I * ((u - w : ℝ) : ℂ)) - 1) := by
    rw [mul_sub, mul_one, ← Complex.exp_add]
    push_cast
    ring_nf
  have hdiff : ‖Complex.exp (Complex.I * (u : ℂ)) - Complex.exp (Complex.I * (w : ℂ))‖
      ≤ |u - w| := by
    rw [hfac, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul]
    simpa [Real.norm_eq_abs] using (Real.norm_exp_I_mul_ofReal_sub_one_le (x := u - w))
  have huw : |u - w| ≤ |t| * ε := by
    have hid : u - w = -(t * (a - c)) := by rw [hu, hw]; ring
    rw [hid, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_left h (abs_nonneg t)
  calc ‖Complex.exp (-(Complex.I * (t * a))) * z - Complex.exp (-(Complex.I * (t * c))) * z‖
      = ‖Complex.exp (Complex.I * (u : ℂ)) - Complex.exp (Complex.I * (w : ℂ))‖ * ‖z‖ := by
        rw [hrw a, hrw c, ← sub_mul, norm_mul]
    _ ≤ (|t| * ε) * ‖z‖ := mul_le_mul_of_nonneg_right (hdiff.trans huw) (norm_nonneg z)
