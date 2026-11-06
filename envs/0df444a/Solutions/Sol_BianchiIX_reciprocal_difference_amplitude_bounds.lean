-- Prove2me | solution 1 for BianchiIX.reciprocal_difference_amplitude_bounds
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T06:59:52.404256+00:00
-- url     : https://prove2.me/submissions/abb8adfb-4973-466f-bc93-6caaee2789a3

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX


/-- The reciprocal correction preserves the two amplitude-sensitive columns. -/
theorem solution {α A D u v Θ ψ : ℝ} {p s : Fin 3 → ℝ}
    (hα : 0 < α ∧ α ≤ 1) (hA : 0 ≤ A) (hD : 0 ≤ D) (hu : 0 ≤ u) (hv : 0 ≤ v ∧ v ≤ 1)
    (hΘ : |Θ| ≤ A * α * u * v) (hψ : |ψ| ≤ 2 * α ^ 2 * |Θ|)
    (hp : |p 0| + |p 1| ≤ A * u * v / α ^ 2) (hp2 : |p 2| ≤ A * u / α ^ 2)
    (hs : ∀ i, |s i| ≤ 2 * α ^ 2 * |p i| + 4 * D * α * |Θ|) :
    |ψ| ≤ 10 * A * (D + 1) * α ^ 3 * u * v ∧
      |s 0| + |s 1| ≤ 10 * A * (D + 1) * u * v ∧
      |s 2| ≤ 10 * A * (D + 1) * u := by
  have hα0 := hα.1
  have hv0 := hv.1
  have hαsq : α ^ 2 ≤ 1 := pow_le_one₀ hα.1.le hα.2
  have HΘ : 4 * D * α * |Θ| ≤ 4 * D * A * u * v := by
    calc
      _ ≤ 4 * D * α * (A * α * u * v) := mul_le_mul_of_nonneg_left hΘ (by positivity)
      _ = (4 * D * A * u * v) * α ^ 2 := by ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) hαsq
  have HP : 2 * α ^ 2 * (|p 0| + |p 1|) ≤ 2 * A * u * v := by
    calc
      _ ≤ 2 * α ^ 2 * (A * u * v / α ^ 2) := mul_le_mul_of_nonneg_left hp (by positivity)
      _ = _ := by field_simp
  have HP2 : 2 * α ^ 2 * |p 2| ≤ 2 * A * u := by
    calc
      _ ≤ 2 * α ^ 2 * (A * u / α ^ 2) := mul_le_mul_of_nonneg_left hp2 (by positivity)
      _ = _ := by field_simp
  refine ⟨?_, ?_, ?_⟩
  · have H := mul_le_mul_of_nonneg_left hΘ (by positivity : 0 ≤ 2 * α ^ 2)
    nlinarith only [hψ, H, mul_nonneg hD (by positivity : 0 ≤ A * α ^ 3 * u * v),
      (by positivity : 0 ≤ A * α ^ 3 * u * v)]
  · nlinarith only [hs 0, hs 1, HΘ, HP, mul_nonneg hD (by positivity : 0 ≤ A * u * v),
      (by positivity : 0 ≤ A * u * v)]
  · have Hv := mul_le_mul_of_nonneg_left hv.2 (by positivity : 0 ≤ 4 * D * A * u)
    nlinarith only [hs 2, HΘ, HP2, Hv, mul_nonneg hD (by positivity : 0 ≤ A * u), mul_nonneg hA hu]
