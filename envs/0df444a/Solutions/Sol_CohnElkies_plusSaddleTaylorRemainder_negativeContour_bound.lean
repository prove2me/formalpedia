-- Prove2me | solution 1 for CohnElkies.plusSaddleTaylorRemainder_negativeContour_bound
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/2cc473b4-20e8-448c-91be-0b2586d5b42d

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleMellinInversePower_shiftedLine_integral_norm
import Theorems.Thm_CohnElkies_saddleTaylorContour_rpow
import Theorems.Thm_CohnElkies_plusSaddleMellinData_negativeContour_integral_norm_le

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology BigOperators
namespace CohnElkies
theorem _root_.solution
    {ε ℓ : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4)
    (hℓ : 0 < ℓ) (N : ℕ)
    (hN : 2 * (((N + 1 : ℕ) : ℝ)) ≤ ℓ)
    (horder : shortCutoff ε ≤ shortEndpoint ε)
    (hmargin : ∀ a ∈ Icc (shortCutoff ε) (shortEndpoint ε),
      0 ≤ shortMargin ε a)
    {r : ℝ} (hr : 0 < r) :
    ‖plusSaddleTaylorRemainder ε ℓ N r‖ ≤
      (1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
        saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMass ε := by
  let a : ℝ := saddleTaylorContour N
  let c : ℂ := ((1 / (2 * Real.pi) : ℝ) : ℂ)
  have hdata : Integrable
      (fun t : ℝ => plusSaddleMellinData ε ℓ
        ((a : ℂ) + (t : ℂ) * Complex.I)) := by
    simpa [a] using!
      plusSaddleMellinData_shiftedLine_moment_integrable
        hε hℓ horder
        (fun n : ℕ => saddleTaylorContour_ne_pole N n) 0
  have hline :=
    plusSaddleMellinData_negativeContour_integral_norm_le
      hε hεsmall hℓ N hN horder hmargin
  have hc : ‖c‖ = 1 / (2 * Real.pi) := by
    try dsimp [c]
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by positivity : 0 < 1 / (2 * Real.pi))]
  unfold plusSaddleTaylorRemainder
  change
    ‖c *
      (∫ t : ℝ,
        saddleMellinInversePower r
          ((a : ℂ) + (t : ℂ) * Complex.I) *
            plusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I))‖ ≤ _
  rw [norm_mul, hc]
  calc
    (1 / (2 * Real.pi)) *
        ‖∫ t : ℝ,
          saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
              plusSaddleMellinData ε ℓ
                ((a : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      (1 / (2 * Real.pi)) *
        (∫ t : ℝ,
          ‖saddleMellinInversePower r
            ((a : ℂ) + (t : ℂ) * Complex.I) *
              plusSaddleMellinData ε ℓ
                ((a : ℂ) + (t : ℂ) * Complex.I)‖) := by
        gcongr
        exact MeasureTheory.norm_integral_le_integral_norm _
    _ = (1 / (2 * Real.pi)) *
        (r ^ (2 * N + 1) *
          (∫ t : ℝ,
            ‖plusSaddleMellinData ε ℓ
              ((a : ℂ) + (t : ℂ) * Complex.I)‖)) := by
      rw [saddleMellinInversePower_shiftedLine_integral_norm
        hr (plusSaddleMellinData ε ℓ) hdata]
      change
        (1 / (2 * Real.pi)) *
          (r ^ (-(saddleTaylorContour N)) * _) = _
      rw [saddleTaylorContour_rpow]
    _ ≤ (1 / (2 * Real.pi)) *
        (r ^ (2 * N + 1) *
          (saddleNegativeMellinMajorantCoefficient ε ℓ N *
            saddleNegativeFrequencyMass ε)) := by
      gcongr
    _ = (1 / (2 * Real.pi)) * r ^ (2 * N + 1) *
          saddleNegativeMellinMajorantCoefficient ε ℓ N *
            saddleNegativeFrequencyMass ε := by ring
end CohnElkies
