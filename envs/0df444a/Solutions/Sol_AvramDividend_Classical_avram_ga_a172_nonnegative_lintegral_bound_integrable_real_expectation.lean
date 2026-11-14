-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a172_nonnegative_lintegral_bound_integrable_real_expectation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:42:19.347914+00:00
-- url     : https://prove2.me/submissions/f8a17a09-5a4d-4a5a-a418-f21c9af36b34

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lintegral_bound_implies_real_integral_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

/-- A finite nonnegative source ENNReal energy bound proves integrability and
the matching real integral upper bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (f : Ω → ℝ) (K : ℝ)
    (hf : Measurable f) (hf0 : ∀ᵐ ω ∂P, 0 ≤ f ω)
    (hK : 0 ≤ K)
    (hBound : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≤ ENNReal.ofReal K) :
    Integrable f P ∧ (∫ ω, f ω ∂P) ≤ K := by
  have hFinite :
      (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) ≠ ⊤ := by
    have hKFinite : ENNReal.ofReal K < ⊤ := ENNReal.ofReal_lt_top
    have hlt : (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) < ⊤ :=
      lt_of_le_of_lt hBound hKFinite
    exact ne_of_lt hlt
  have hInt : Integrable f P :=
    (lintegral_ofReal_ne_top_iff_integrable hf.aestronglyMeasurable hf0).mp hFinite
  refine ⟨hInt,?_⟩
  exact chat03_lintegral_bound_implies_real_integral_bound
    P f K hInt hf0 hK hBound
