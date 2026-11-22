-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_compactband_chronological_mark_Taylor_expected_positive_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T14:42:12.608182+00:00
-- url     : https://prove2.me/submissions/9e1c31fb-6128-4f3b-947c-616636adb0be

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_chronological_mark_Taylor_expected_positive_zero
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_compact_two_reserve_negative_mark_Taylor_abs_bound
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (c : ℝ)
    (hc : 0 < c) (hcC : ENNReal.ofReal c ≤ C)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (n : ℕ) (S : Ω → Finset ℝ≥0)
    (hSpos : ∀ ω t, t ∈ S ω → 0 < t)
    (hSneg : ∀ ω t, t ∈ S ω →
      X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0)
    (hSinterior : ∀ ω t, t ∈ S ω →
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω ∈
        Ioo (0 : ℝ) c)
    (hCount : ∀ᵐ ω ∂P, ((S ω).card : ℝ) ≤
      (((Measure.count.restrict {t : ℝ≥0 |
        0 < t ∧ X.X t ω -
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) t ≠ 0}).map
          (fun t : ℝ≥0 => (t,
            X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)))
          (Ioc 0 (n : ℝ≥0) ×ˢ Iio (0 : ℝ))).toReal)
    (grid : ℕ → Ω → ℝ≥0 → ℝ≥0)
    (hgrid : ∀ᵐ ω ∂P, ∀ t ∈ S ω,
      Tendsto (fun m => grid m ω t) atTop (𝓝[<] t))
    (E : ℕ → Ω → ℝ≥0 → ℝ)
    (hEsource : ∀ m ω t,
      E m ω t =
        let y := x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t -
          D t ω
        let z := X.X t ω -
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
        let u := x + X.X (grid m ω t) ω -
          rightLimit D (grid m ω t) ω
        ((w (u + z) - w u -
          (if -1 < z then z * deriv w u else 0)) -
         (w (y + z) - w y -
          (if -1 < z then z * deriv w y else 0))))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {r : ℝ | 0 < r ∧ ENNReal.ofReal r < C})
    (hPreband : ∀ ω t, t ∈ S ω →
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω ∈ Icc a b)
    (hSample : ∀ m ω t, t ∈ S ω →
      x + X.X (grid m ω t) ω -
        rightLimit D (grid m ω t) ω ∈ Icc a b)
    (hMeas : ∀ m, AEStronglyMeasurable
      (fun ω => max (∑ t ∈ S ω, E m ω t) 0) P) :
    Tendsto
      (fun m => ∫ ω, max (∑ t ∈ S ω, E m ω t) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  obtain ⟨L, hL, hKernel⟩ :=
    avram_freshD_original_compact_two_reserve_negative_mark_Taylor_abs_bound
      C w hwcont hwneg hw_smooth a b ha hab hBand
  have hEBound : ∀ m ω t, t ∈ S ω → |E m ω t| ≤ L := by
    intro m ω t ht
    rw [hEsource m ω t]
    exact hKernel
      (x + X.X (grid m ω t) ω -
        rightLimit D (grid m ω t) ω) (hSample m ω t ht)
      (x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t -
        D t ω) (hPreband ω t ht)
      (X.X t ω -
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) t)
      (hSneg ω t ht)
  exact avram_freshD_original_chronological_mark_Taylor_expected_positive_zero
    X hFinite x D hD w C c hc hcC hw_smooth hw0 hwcont hwneg
    n S hSpos hSneg hSinterior hCount grid hgrid
    E hEsource L hL hEBound hMeas
