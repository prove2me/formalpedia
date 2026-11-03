-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_19_original_boundary_preserved_monotone_interior_lintegral_iSup
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T20:23:28.345844+00:00
-- url     : https://prove2.me/submissions/c992452c-89cd-4324-b074-897a31228523

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
/-- Every source ruin payment is covered by cap support or an increasing interior window. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (boundary : Set ℝ) (interior : ℕ → Set ℝ)
    (hBoundaryMeas : MeasurableSet boundary)
    (hInteriorMeas : ∀ n, MeasurableSet (interior n))
    (hInteriorMon : Monotone interior)
    (hCover : paymentTimes (ruinTime X x D ω) ∩ Iic T ⊆
      ⋃ n : ℕ, boundary ∪ interior n) :
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
    (⨆ n : ℕ, (∫⁻ t in boundary ∪ interior n,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  classical
  let μ : Measure ℝ := dividendMeasure D ω
  let f : ℝ → ℝ≥0∞ := fun t => ENNReal.ofReal (Real.exp (-(q * t)))
  let U : ℕ → Set ℝ := fun n => boundary ∪ interior n
  have hUmeas : ∀ n, MeasurableSet (U n) := by
    intro n
    exact hBoundaryMeas.union (hInteriorMeas n)
  have hUmon : Monotone U := by
    intro n m hnm t ht
    rcases ht with hb | hi
    · exact Or.inl hb
    · exact Or.inr (hInteriorMon hnm hi)
  have hf : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      (Real.measurable_exp.comp (measurable_const.mul measurable_id).neg)
  have hGmeas : ∀ n, Measurable ((U n).indicator f) := by
    intro n
    exact hf.indicator (hUmeas n)
  have hGmon : Monotone (fun n : ℕ => (U n).indicator f) := by
    intro n m hnm
    exact Set.indicator_le_indicator_of_subset (hUmon hnm) (fun t => bot_le)
  have hConst : Monotone (fun _ : ℕ => f) := by
    intro n m hnm
    exact le_refl f
  have hSupIndicator :
      (⨆ n : ℕ, (U n).indicator f) = (⋃ n : ℕ, U n).indicator f := by
    simpa only [iSup_const] using
      (Set.iSup_indicator (show (⊥ : ℝ≥0∞) = 0 by rfl) hConst hUmon)
  have hUnionMeas : MeasurableSet (⋃ n : ℕ, U n) :=
    MeasurableSet.iUnion hUmeas
  have hMassSup :
      (∫⁻ t in ⋃ n : ℕ, U n, f t ∂μ) =
      ⨆ n : ℕ, (∫⁻ t in U n, f t ∂μ) := by
    calc
      (∫⁻ t in ⋃ n : ℕ, U n, f t ∂μ) =
          ∫⁻ t, ((⋃ n : ℕ, U n).indicator f) t ∂μ :=
        (lintegral_indicator hUnionMeas f).symm
      _ = ∫⁻ t, (⨆ n : ℕ, ((U n).indicator f) t) ∂μ := by
        rw [← hSupIndicator]
        simp only [iSup_apply]
      _ = ⨆ n : ℕ, (∫⁻ t, ((U n).indicator f) t ∂μ) :=
        lintegral_iSup hGmeas hGmon
      _ = ⨆ n : ℕ, (∫⁻ t in U n, f t ∂μ) := by
        congr 1
        funext n
        exact lintegral_indicator (hUmeas n) f
  change (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      f t ∂μ) ≤ (⨆ n : ℕ, (∫⁻ t in U n, f t ∂μ))
  calc
    (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T, f t ∂μ) ≤
        (∫⁻ t in ⋃ n : ℕ, U n, f t ∂μ) := by
      exact lintegral_mono_set hCover
    _ = ⨆ n : ℕ, (∫⁻ t in U n, f t ∂μ) := hMassSup
