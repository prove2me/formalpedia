-- Prove2me | solution 1 for Formalism.DimensionVariation.fjMoment
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:06:39.378898+00:00
-- url     : https://prove2.me/submissions/7c456a80-8852-40da-8af9-e25aa68083a1

import Mathlib
import Definitions.Def_Formalism_ThetaSupremumBounds_StatementA
import Definitions.Def_Formalism_ThetaSupremumBounds_GaussianShiftBounds_FockJet

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset MeasureTheory Filter Topology
open scoped ComplexConjugate Real Nat
noncomputable section
open Formalism Formalism.DimensionVariation
namespace Formalism.DimensionVariation
theorem _root_.solution (b : ℝ) (hb : 0 < b) (n : ℕ) :
    Integrable (fun z : ℂ => ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2)) ∧
    ∫ z : ℂ, ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2) =
      π * b ^ (-((n : ℝ) + 2) / 2) * Real.Gamma (((n : ℝ) + 2) / 2) := by
  have hval : ∫ z : ℂ, ‖z‖ ^ n * Real.exp (-b * ‖z‖ ^ 2) =
      π * b ^ (-((n : ℝ) + 2) / 2) * Real.Gamma (((n : ℝ) + 2) / 2) := by
    have h := Complex.integral_rpow_mul_exp_neg_mul_rpow (p := 2) (q := (n : ℝ)) (b := b)
      (by norm_num) (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]) hb
    simp only [Real.rpow_two, Real.rpow_natCast] at h
    rw [h]
    ring
  refine ⟨Integrable.of_integral_ne_zero ?_, hval⟩
  rw [hval]
  have h1 : 0 < b ^ (-((n : ℝ) + 2) / 2) := Real.rpow_pos_of_pos hb _
  have h2 : 0 < Real.Gamma (((n : ℝ) + 2) / 2) := Real.Gamma_pos_of_pos (by positivity)
  exact (mul_pos (mul_pos Real.pi_pos h1) h2).ne'
end Formalism.DimensionVariation
