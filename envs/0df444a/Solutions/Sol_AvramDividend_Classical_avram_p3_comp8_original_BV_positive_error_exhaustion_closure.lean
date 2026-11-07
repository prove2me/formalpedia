-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_comp8_original_BV_positive_error_exhaustion_closure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T13:36:35.475045+00:00
-- url     : https://prove2.me/submissions/04272cbd-1855-4506-ae70-f3bf198899fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_mass_exhaustion_L1_tail
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_measurable_event_split
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_positive_error_moving_event_tail_absorption

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (K : ℝ) (hK : 0 ≤ K)
    (s : ℕ → Set Ω) (hs : ∀ n, MeasurableSet (s n))
    (hExhaust : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, ω ∈ s n)
    (Err : ℕ → Ω → ℝ)
    (hPos : ∀ n, Integrable (fun ω => max (Err n ω) 0) P)
    (hLocal : Tendsto
      (fun n => ∫ ω, max (if ω ∈ s n then Err n ω else 0) 0 ∂P)
      atTop (nhds (0 : ℝ)))
    (hTailBound : ∀ n, ∀ᵐ ω ∂P,
      max (if ω ∉ s n then Err n ω else 0) 0 ≤
        (if ω ∈ s n then 0 else
          K * (|X.drift| * (T : ℝ) +
            |(T : ℝ) * X.drift - X.X T ω|))) :
    Tendsto
      (fun n => ∫ ω, max (Err n ω) 0 ∂P)
      atTop (nhds (0 : ℝ)) := by
  obtain ⟨hEnvelopeI, hEnvelopeLim⟩ :=
    avram_bv_error7_original_BV_source_mass_exhaustion_L1_tail
      X hX hBV T hT K hK s hs hExhaust
  have hTailI : ∀ n,
      Integrable (fun ω => max (if ω ∉ s n then Err n ω else 0) 0) P := by
    intro n
    exact (avram_bv_error7_positive_error_measurable_event_split
      P (s n) (hs n) (Err n) (hPos n)).2.1
  have hTailLe : ∀ n,
      (∫ ω, max (if ω ∉ s n then Err n ω else 0) 0 ∂P) ≤
      (∫ ω, if ω ∈ s n then 0 else
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|) ∂P) := by
    intro n
    exact integral_mono_ae (hTailI n) (hEnvelopeI n) (hTailBound n)
  have hTailNonneg : ∀ n,
      0 ≤ ∫ ω, max (if ω ∉ s n then Err n ω else 0) 0 ∂P := by
    intro n
    apply integral_nonneg
    intro ω
    exact le_max_right _ _
  have hTailLim :
      Tendsto (fun n => ∫ ω,
        max (if ω ∉ s n then Err n ω else 0) 0 ∂P)
        atTop (nhds (0 : ℝ)) :=
    squeeze_zero hTailNonneg hTailLe hEnvelopeLim
  exact avram_bv_error7_positive_error_moving_event_tail_absorption
    P s hs Err hPos hLocal hTailLim
