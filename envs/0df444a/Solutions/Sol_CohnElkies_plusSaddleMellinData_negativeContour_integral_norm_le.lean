-- Prove2me | solution 1 for CohnElkies.plusSaddleMellinData_negativeContour_integral_norm_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:28.839589+00:00
-- url     : https://prove2.me/submissions/fea25a2f-5181-415c-a361-d982353797a0

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_saddleNegativeFrequencyMajorant_integrable
import Theorems.Thm_CohnElkies_plusSaddleMellinData_negativeContour_norm_le

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
      0 ≤ shortMargin ε a) :
    (∫ s : ℝ,
      ‖plusSaddleMellinData ε ℓ
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)‖) ≤
      saddleNegativeMellinMajorantCoefficient ε ℓ N *
        saddleNegativeFrequencyMass ε := by
  have hdata : Integrable
      (fun s : ℝ =>
        plusSaddleMellinData ε ℓ
          ((saddleTaylorContour N : ℂ) +
            (s : ℂ) * Complex.I)) := by
    simpa using!
      plusSaddleMellinData_shiftedLine_moment_integrable
        hε hℓ horder
        (fun n : ℕ => saddleTaylorContour_ne_pole N n) 0
  have hmajor : Integrable
      (fun s : ℝ =>
        saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMajorant ε s) :=
    (saddleNegativeFrequencyMajorant_integrable hε).const_mul
      (saddleNegativeMellinMajorantCoefficient ε ℓ N)
  calc
    (∫ s : ℝ,
      ‖plusSaddleMellinData ε ℓ
        ((saddleTaylorContour N : ℂ) +
          (s : ℂ) * Complex.I)‖) ≤
      ∫ s : ℝ,
        saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMajorant ε s := by
        apply integral_mono hdata.norm hmajor
        intro s
        exact plusSaddleMellinData_negativeContour_norm_le
          hε hεsmall hℓ N hN horder hmargin s
    _ = saddleNegativeMellinMajorantCoefficient ε ℓ N *
          saddleNegativeFrequencyMass ε := by
      rw [integral_const_mul]
      rfl
end CohnElkies
