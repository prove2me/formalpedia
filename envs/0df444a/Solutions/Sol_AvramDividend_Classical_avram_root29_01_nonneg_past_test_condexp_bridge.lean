-- Prove2me | solution 1 for AvramDividend.Classical.avram_root29_01_nonneg_past_test_condexp_bridge
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T10:30:18.836875+00:00
-- url     : https://prove2.me/submissions/fcf30397-5892-4b89-82f8-df1247d6b40d

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Basic

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
attribute [local instance] Classical.propDecidable

/-- Equal nonnegative ENNReal tests against every past event determine the
genuine real conditional expectation, with real integrability explicit. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (𝓖 : MeasurableSpace Ω) (h𝓖 : 𝓖 ≤ mΩ)
    [SigmaFinite (P.trim h𝓖)]
    (f g : Ω → ℝ) (hf : Integrable f P) (hg : Integrable g P)
    (hgm : Measurable[𝓖] g)
    (hfnn : 0 ≤ᵐ[P] f) (hgnn : 0 ≤ᵐ[P] g)
    (hTest : ∀ A : Set Ω, MeasurableSet[𝓖] A →
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (f ω)
        else (0 : ℝ≥0∞) ∂P) =
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (g ω)
        else (0 : ℝ≥0∞) ∂P)) :
    P[f | 𝓖] =ᵐ[P] g := by
  have hSet (A : Set Ω) (hA : MeasurableSet[𝓖] A) :
      MeasurableSet[mΩ] A := h𝓖 A hA
  have hIndN (u : Ω → ℝ) (hu : 0 ≤ᵐ[P] u)
      (A : Set Ω) : 0 ≤ᵐ[P] A.indicator u := by
    filter_upwards [hu] with ω hω
    by_cases hmem : ω ∈ A
    · simpa [Set.indicator_of_mem hmem] using hω
    · simp [Set.indicator_of_notMem hmem]
  have hLift (u : Ω → ℝ) (hu : Integrable u P)
      (huN : 0 ≤ᵐ[P] u)
      (A : Set Ω) (hA : MeasurableSet[𝓖] A) :
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (u ω)
        else (0 : ℝ≥0∞) ∂P) =
        ENNReal.ofReal (∫ ω in A, u ω ∂P) := by
    have hUi : Integrable (A.indicator u) P :=
      hu.indicator (hSet A hA)
    calc
      (∫⁻ ω, if ω ∈ A then ENNReal.ofReal (u ω) else 0 ∂P) =
          ∫⁻ ω, ENNReal.ofReal (A.indicator u ω) ∂P := by
        apply lintegral_congr
        intro ω
        by_cases hω : ω ∈ A
        · simp only [if_pos hω, Set.indicator_of_mem hω]
        · simp only [if_neg hω, Set.indicator_of_notMem hω,
            ENNReal.ofReal_zero]
      _ = ENNReal.ofReal (∫ ω, A.indicator u ω ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hUi (hIndN u huN A)).symm
      _ = ENNReal.ofReal (∫ ω in A, u ω ∂P) := by
        rw [integral_indicator (hSet A hA)]
  have hSetEq (A : Set Ω) (hA : MeasurableSet[𝓖] A) :
      (∫ ω in A, g ω ∂P) = ∫ ω in A, f ω ∂P := by
    have hfEq := hLift f hf hfnn A hA
    have hgEq := hLift g hg hgnn A hA
    have hh : ENNReal.ofReal (∫ ω in A, f ω ∂P) =
        ENNReal.ofReal (∫ ω in A, g ω ∂P) := by
      calc
        _ = ∫⁻ ω, if ω ∈ A then ENNReal.ofReal (f ω) else 0 ∂P :=
          hfEq.symm
        _ = ∫⁻ ω, if ω ∈ A then ENNReal.ofReal (g ω) else 0 ∂P :=
          hTest A hA
        _ = _ := hgEq
    have hfn : 0 ≤ (∫ ω in A, f ω ∂P) := by
      rw [← integral_indicator (hSet A hA)]
      exact integral_nonneg_of_ae (hIndN f hfnn A)
    have hgn : 0 ≤ (∫ ω in A, g ω ∂P) := by
      rw [← integral_indicator (hSet A hA)]
      exact integral_nonneg_of_ae (hIndN g hgnn A)
    have hh' := congrArg ENNReal.toReal hh
    simpa only [ENNReal.toReal_ofReal hfn, ENNReal.toReal_ofReal hgn] using hh'.symm
  exact (ae_eq_condExp_of_forall_setIntegral_eq h𝓖 hf
    (fun A _ _ => hg.integrableOn)
    (fun A hA _ => hSetEq A hA)
    hgm.aestronglyMeasurable).symm
