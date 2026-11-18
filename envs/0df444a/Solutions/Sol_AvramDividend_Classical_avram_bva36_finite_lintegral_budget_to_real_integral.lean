-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva36_finite_lintegral_budget_to_real_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T22:11:23.891187+00:00
-- url     : https://prove2.me/submissions/3ebbd7d8-5dd1-4c2e-bd79-98f1ebb3fa56

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ≥0∞) (K : ℝ)
    (hFin : ∀ ω, f ω ≠ ⊤)
    (hI : Integrable (fun ω => (f ω).toReal) P)
    (hK : 0 ≤ K)
    (hBudget : (∫⁻ ω, f ω ∂P) ≤ ENNReal.ofReal K) :
    (∫ ω, (f ω).toReal ∂P) ≤ K := by
  have hNonneg : 0 ≤ᵐ[P] (fun ω => (f ω).toReal) :=
    Filter.Eventually.of_forall (fun ω => ENNReal.toReal_nonneg)
  have hEq : ENNReal.ofReal (∫ ω, (f ω).toReal ∂P) =
      ∫⁻ ω, f ω ∂P := by
    rw [ofReal_integral_eq_lintegral_ofReal hI hNonneg]
    apply lintegral_congr
    intro ω
    exact ENNReal.ofReal_toReal (hFin ω)
  exact (ENNReal.ofReal_le_ofReal_iff hK).mp (hEq.le.trans hBudget)
