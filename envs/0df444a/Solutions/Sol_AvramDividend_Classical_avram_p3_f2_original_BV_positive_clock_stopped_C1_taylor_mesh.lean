-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_BV_positive_clock_stopped_C1_taylor_mesh
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:02:19.017719+00:00
-- url     : https://prove2.me/submissions/556f4a56-c240-47dc-ba44-76b77fd93b64

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_interior_C1_source_cell_taylor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Genuine BV positive-time source grids obey the original C1 Taylor remainder bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ᵐ ω ∂P, ∀ (s t : ℝ≥0), 0 < s →
      ∀ ε : ℝ, 0 < ε →
        ∃ δ : ℝ, 0 < δ ∧
        ∀ (u : ℕ → ℝ≥0) (n : ℕ),
          let J : ℝ≥0 → ℝ := fun r =>
            ∑' v : ℝ≥0, if 0 < v ∧ v ≤ r then
              Function.leftLim (fun q : ℝ≥0 => X.X q ω) v - X.X v ω else 0
          let Y : ℝ≥0 → ℝ := fun r => X.X r ω + J r
          let z : ℕ → ℝ := fun i =>
            x + X.X (u i) ω - rightLimit D (u i) ω
          let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
          (∀ i, i < n →
            u i ∈ Set.Icc s t ∧ u (i + 1) ∈ Set.Icc s t) →
          (∀ i, i < n → dist (u (i + 1)) (u i) < δ) →
          (∀ i, i < n →
            Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
          ∀ i, i < n →
            |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
              ε * |c i| := by
  have hCont : ContinuousOn (deriv w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.continuousOn_deriv_of_isOpen hOpen (by norm_num)
  have hUnif : UniformContinuousOn (deriv w) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hCont.mono hBand)
  filter_upwards [avram_p3_f2_original_positive_compact_physical_Y_cell_modulus
    X hBV] with ω hY
  intro s t hs ε hε
  obtain ⟨η, hη, hControl⟩ :=
    (Metric.uniformContinuousOn_iff.mp hUnif) ε hε
  obtain ⟨δ, hδ, hYstep⟩ := hY s t hs η hη
  refine ⟨δ, hδ, ?_⟩
  intro u n J Y z c hTime hStep hInside
  have hSmall : ∀ i, i < n → |c i| < η := by
    intro i hi
    exact hYstep u n hTime hStep i hi
  have hInsideU : ∀ i, i < n →
      Set.uIcc (z i) (z i + c i) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro i hi
    exact (hInside i hi).trans hBand
  have hInt : ∀ i, i < n →
      IntervalIntegrable (deriv w) volume (z i) (z i + c i) := by
    intro i hi
    exact (hCont.mono ((hInside i hi).trans hBand)).intervalIntegrable
  have hOsc : ∀ i, i < n → ∀ v ∈ Set.uIoc (z i) (z i + c i),
      |deriv w v - deriv w (z i)| ≤ ε := by
    intro i hi v hv
    have hvIcc : v ∈ Set.uIcc (z i) (z i + c i) :=
      Set.uIoc_subset_uIcc hv
    have hzBand : z i ∈ Set.Icc a b :=
      hInside i hi Set.left_mem_uIcc
    have hdist : dist v (z i) < η := by
      rw [Real.dist_eq]
      calc
        |v - z i| ≤ |(z i + c i) - z i| :=
          Set.abs_sub_left_of_mem_uIcc hvIcc
        _ = |c i| := by simp only [add_sub_cancel_left]
        _ < η := hSmall i hi
    exact le_of_lt (by
      simpa only [Real.dist_eq] using
        hControl v (hInside i hi hvIcc) (z i) hzBand hdist)
  exact avram_p3_f2_original_stopped_interior_C1_source_cell_taylor
    X x C D hD w hwC1 hOpen ω u n ε hInsideU hInt hOsc
