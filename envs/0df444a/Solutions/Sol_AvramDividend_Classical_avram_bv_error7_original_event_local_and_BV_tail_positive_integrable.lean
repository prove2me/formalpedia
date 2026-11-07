-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_error7_original_event_local_and_BV_tail_positive_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T17:55:50.170953+00:00
-- url     : https://prove2.me/submissions/503de8b0-4e52-46ac-beef-2763d925dcab

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_error7_original_BV_source_variation_L1_upto_one
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- Integrable positive original grid errors on one interior event and
the integrable authentic BV source mass suffice for global L1 control. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (T : ℝ≥0) (hT : T ≤ 1)
    (s : Set Ω) (Err : ℕ → Ω → ℝ)
    (hMaskedInt : ∀ m, Integrable
      (fun ω => max (if ω ∈ s then Err m ω else 0) 0) P)
    (hPosMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (Err m ω) 0) P)
    (K : ℝ) (hK : 0 ≤ K)
    (hOutside : ∀ m, ∀ᵐ ω ∂P, ω ∉ s →
      max (Err m ω) 0 ≤
        K * (|X.drift| * (T : ℝ) +
          |(T : ℝ) * X.drift - X.X T ω|)) :
    ∀ m, Integrable (fun ω => max (Err m ω) 0) P := by
  let H : Ω → ℝ := fun ω =>
    K * (|X.drift| * (T : ℝ) +
      |(T : ℝ) * X.drift - X.X T ω|)
  have hBase : Integrable (fun ω =>
      |X.drift| * (T : ℝ) +
        |(T : ℝ) * X.drift - X.X T ω|) P :=
    (avram_bv_error7_original_BV_source_variation_L1_upto_one
      X hX hBV T hT).1
  have hH : Integrable H P := hBase.const_mul K
  intro m
  have hMajor : Integrable (fun ω =>
      ‖max (if ω ∈ s then Err m ω else 0) 0‖ + H ω) P :=
    (hMaskedInt m).norm.add hH
  have hBound : ∀ᵐ ω ∂P,
      ‖max (Err m ω) 0‖ ≤
        ‖max (if ω ∈ s then Err m ω else 0) 0‖ + H ω := by
    filter_upwards [hOutside m] with ω hout
    have hHnonneg : 0 ≤ H ω := by
      dsimp [H]
      positivity
    by_cases hs : ω ∈ s
    · simpa only [if_pos hs] using
        (le_add_of_nonneg_right hHnonneg :
          ‖max (Err m ω) 0‖ ≤ ‖max (Err m ω) 0‖ + H ω)
    · have hmax : 0 ≤ max (Err m ω) 0 := le_max_right _ _
      have hcore := hout hs
      simpa [hs, H, Real.norm_eq_abs, abs_of_nonneg hmax] using hcore
  exact hMajor.mono' (hPosMeas m) hBound
