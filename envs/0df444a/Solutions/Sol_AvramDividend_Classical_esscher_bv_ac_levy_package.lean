-- Prove2me | solution 1 for AvramDividend.Classical.esscher_bv_ac_levy_package
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T22:56:44.342819+00:00
-- url     : https://prove2.me/submissions/f0d78e34-58fc-4a24-b49d-03b844c92e50

import Mathlib
import Theorems.Thm_AvramDividend_Classical_esscher_weighted_levy_measure_support_ac
import Theorems.Thm_AvramDividend_Classical_esscher_negative_jumps_levy_integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal

/-- Package the three Lévy-measure invariants of a positive Esscher shift. -/
theorem solution
    (ν : Measure ℝ) (φ : ℝ) (hφ : 0 ≤ φ)
    (hneg : ν (Ici 0) = 0) (hac : ν ≪ volume)
    (hlevy : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Ici 0) = 0 ∧
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) ≪ volume ∧
    (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2))
      ∂(ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))) < ⊤ := by
  obtain ⟨hsupport, habs⟩ :=
    esscher_weighted_levy_measure_support_ac ν φ hneg hac
  exact ⟨hsupport, habs,
    esscher_negative_jumps_levy_integrable ν φ hφ hneg hlevy⟩
