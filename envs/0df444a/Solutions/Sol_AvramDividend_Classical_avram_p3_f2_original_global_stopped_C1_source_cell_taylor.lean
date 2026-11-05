-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_global_stopped_C1_source_cell_taylor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:06:16.48105+00:00
-- url     : https://prove2.me/submissions/4549af26-de17-425b-b916-8e59318252f2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_global_positive_cap_C1_source_mesh_modulus
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_interior_C1_source_cell_taylor
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- A shared positive mesh threshold bounds every original interior source-cell C1 remainder. -/
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
          |w (z i + c i) - w (z i) - deriv w (z i) * c i| ≤
            ε * |c i| := by
  intro ε hε
  obtain ⟨δ, hδ, hMod⟩ :=
    avram_p3_f2_original_global_positive_cap_C1_source_mesh_modulus
      X x C D hD w hwC1 hOpen a b hBand ε hε
  refine ⟨δ, hδ, ?_⟩
  intro ω u n J Y z c hInside hSmall
  have hInsideU : ∀ i, i < n →
      Set.uIcc (z i) (z i + c i) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro i hi
    exact (hInside i hi).trans hBand
  have hModCells := hMod ω u n hInside hSmall
  have hInt : ∀ i, i < n →
      IntervalIntegrable (deriv w) volume (z i) (z i + c i) := by
    intro i hi
    exact (hModCells i hi).1
  have hOsc : ∀ i, i < n → ∀ v ∈ Set.uIoc (z i) (z i + c i),
      |deriv w v - deriv w (z i)| ≤ ε := by
    intro i hi v hv
    exact (hModCells i hi).2 v hv
  exact avram_p3_f2_original_stopped_interior_C1_source_cell_taylor
    X x C D hD w hwC1 hOpen ω u n ε hInsideU hInt hOsc
