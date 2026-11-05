-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_global_positive_cap_C1_source_mesh_modulus
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T18:52:44.149917+00:00
-- url     : https://prove2.me/submissions/68d0eec8-d7d0-4c50-bfd8-8cbc4296d543

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- One positive C1 modulus works uniformly across all original physical source meshes. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hBand : Set.Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      ∀ (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ),
        let J : ℝ≥0 → ℝ := fun t =>
          ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
            Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
        let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
        let z : ℕ → ℝ := fun i =>
          x + X.X (u i) ω - rightLimit D (u i) ω
        let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
        (∀ i, i < n →
          Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
        (∀ i, i < n → |c i| < δ) →
        ∀ i, i < n →
          IntervalIntegrable (deriv w) volume (z i) (z i + c i) ∧
          ∀ v ∈ Set.uIoc (z i) (z i + c i),
            |deriv w v - deriv w (z i)| ≤ ε := by
  have hCont : ContinuousOn (deriv w)
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hwC1.continuousOn_deriv_of_isOpen hOpen (by norm_num)
  have hUnif : UniformContinuousOn (deriv w) (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous (hCont.mono hBand)
  intro ε hε
  rcases (Metric.uniformContinuousOn_iff.mp hUnif) ε hε with
    ⟨δ, hδ, hControl⟩
  refine ⟨δ, hδ, ?_⟩
  intro ω u n J Y z c hInside hSmall i hi
  have hCell : Set.uIcc (z i) (z i + c i) ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    (hInside i hi).trans hBand
  refine ⟨(hCont.mono hCell).intervalIntegrable, ?_⟩
  intro v hv
  have hvIcc : v ∈ Set.uIcc (z i) (z i + c i) :=
    Set.uIoc_subset_uIcc hv
  have hzBand : z i ∈ Set.Icc a b :=
    hInside i hi Set.left_mem_uIcc
  have hdist : dist v (z i) < δ := by
    rw [Real.dist_eq]
    calc
      |v - z i| ≤ |(z i + c i) - z i| :=
        Set.abs_sub_left_of_mem_uIcc hvIcc
      _ = |c i| := by simp only [add_sub_cancel_left]
      _ < δ := hSmall i hi
  exact le_of_lt (by
    simpa only [Real.dist_eq] using
      hControl v (hInside i hi hvIcc) (z i) hzBand hdist)
