-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f8_nonnegative_integrable_lintegral_toReal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:39:38.550184+00:00
-- url     : https://prove2.me/submissions/3d7168e8-9dc9-4df4-bfd6-843c8f8ee7b2

import Mathlib.MeasureTheory.Integral.Bochner.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Real nonnegative integrability identifies the two expectation encodings. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (f : Ω → ℝ)
    (hf : Integrable f P) (hf0 : ∀ ω, 0 ≤ f ω) :
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂P).toReal = ∫ ω, f ω ∂P := by
  have heq :
      ENNReal.ofReal (∫ ω, f ω ∂P) =
        (∫⁻ ω, ENNReal.ofReal (f ω) ∂P) :=
    ofReal_integral_eq_lintegral_ofReal hf (Filter.Eventually.of_forall hf0)
  calc
    (∫⁻ ω, ENNReal.ofReal (f ω) ∂P).toReal =
      (ENNReal.ofReal (∫ ω, f ω ∂P)).toReal := congrArg ENNReal.toReal heq.symm
    _ = ∫ ω, f ω ∂P := ENNReal.toReal_ofReal (integral_nonneg hf0)
