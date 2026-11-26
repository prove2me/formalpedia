-- Prove2me | solution 1 for FirstPassageLinearTransport.entropy_add_logLikelihood_le_zero
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T11:52:46.439091+00:00
-- url     : https://prove2.me/submissions/80f60c27-8a33-472c-91ac-18dd020dd101

import Definitions.Def_FirstPassageLinearTransport_SharpEntropyBarrier
import Mathlib.Analysis.Complex.ExponentialBounds
import Definitions.Def_FirstPassageLinearTransport_FiniteBallot

set_option autoImplicit true
open FirstPassageLinearTransport
open scoped BigOperators Real
noncomputable section
namespace FirstPassageLinearTransport
theorem _root_.solution
    {p u : ℝ} (hp₀ : 0 < p) (hp₁ : p < 1)
    (hu₀ : 0 < u) (hu₁ : u < 1) :
    Real.binEntropy u + u * Real.log p +
        (1 - u) * Real.log (1 - p) ≤ 0 := by
  have hpComp : 0 < 1 - p := sub_pos.mpr hp₁
  have huComp : 0 < 1 - u := sub_pos.mpr hu₁
  have hleft := Real.log_le_sub_one_of_pos (div_pos hp₀ hu₀)
  have hright := Real.log_le_sub_one_of_pos (div_pos hpComp huComp)
  have hleft' :
      u * Real.log (p / u) ≤ p - u := by
    calc
      u * Real.log (p / u) ≤ u * (p / u - 1) :=
        mul_le_mul_of_nonneg_left hleft hu₀.le
      _ = p - u := by field_simp [hu₀.ne']
  have hright' :
      (1 - u) * Real.log ((1 - p) / (1 - u)) ≤ u - p := by
    calc
      (1 - u) * Real.log ((1 - p) / (1 - u)) ≤
          (1 - u) * ((1 - p) / (1 - u) - 1) :=
        mul_le_mul_of_nonneg_left hright huComp.le
      _ = u - p := by
        field_simp [huComp.ne']
        ring
  calc
    Real.binEntropy u + u * Real.log p +
        (1 - u) * Real.log (1 - p) =
        u * Real.log (p / u) +
          (1 - u) * Real.log ((1 - p) / (1 - u)) := by
      rw [Real.binEntropy, Real.log_inv, Real.log_inv,
        Real.log_div hp₀.ne' hu₀.ne',
        Real.log_div hpComp.ne' huComp.ne']
      ring
    _ ≤ (p - u) + (u - p) := add_le_add hleft' hright'
    _ = 0 := by ring
end FirstPassageLinearTransport
