-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f8_generic_bounded_lintegral_real_transfer
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T12:34:46.175439+00:00
-- url     : https://prove2.me/submissions/06f97e51-9227-460c-b5f1-77fae9d5cdc7

import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.MeasureTheory.Measure.Typeclasses.Probability
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory
open scoped ENNReal
noncomputable section

/-- Transfer a bounded nonnegative pathwise comparison through a probability lintegral. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (a : ℝ) (ha : 0 ≤ a)
    (f g : Ω → ℝ≥0∞)
    (hf : ∀ ω, f ω ≤ 1)
    (hg : ∀ ω, g ω ≤ ENNReal.ofReal a)
    (hfg : ∀ ω, ENNReal.ofReal a * f ω ≤ g ω) :
    a * (∫⁻ ω, f ω ∂P).toReal ≤ (∫⁻ ω, g ω ∂P).toReal := by
  have hfint : (∫⁻ ω, f ω ∂P) < ⊤ := by
    calc
      (∫⁻ ω, f ω ∂P) ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P :=
        lintegral_mono hf
      _ = 1 := by simp
      _ < ⊤ := by norm_num
  have hgint : (∫⁻ ω, g ω ∂P) < ⊤ := by
    calc
      (∫⁻ ω, g ω ∂P) ≤ ∫⁻ _ : Ω, ENNReal.ofReal a ∂P :=
        lintegral_mono hg
      _ = ENNReal.ofReal a := by simp
      _ < ⊤ := ENNReal.ofReal_lt_top
  have hineq :
      ENNReal.ofReal a * (∫⁻ ω, f ω ∂P) ≤ (∫⁻ ω, g ω ∂P) := by
    calc
      ENNReal.ofReal a * (∫⁻ ω, f ω ∂P) =
        ∫⁻ ω, ENNReal.ofReal a * f ω ∂P := by
          rw [lintegral_const_mul' (ENNReal.ofReal a) f
            (ne_top_of_lt ENNReal.ofReal_lt_top)]
      _ ≤ (∫⁻ ω, g ω ∂P) := lintegral_mono hfg
  have hr := ENNReal.toReal_mono (ne_top_of_lt hgint) hineq
  simpa [ENNReal.toReal_mul, ENNReal.toReal_ofReal ha] using hr
