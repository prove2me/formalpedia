-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_f2_original_stopped_uniform_interior_C1_mesh_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T19:17:10.684436+00:00
-- url     : https://prove2.me/submissions/83434911-20fe-46aa-844c-959e21628bf1

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_f2_original_stopped_uniform_interior_C1_mesh_positive_delta
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

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
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (ω : Ω) (u : ℕ → ℝ≥0) (n : ℕ) :
    let J : ℝ≥0 → ℝ := fun t =>
      ∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
        Function.leftLim (fun r : ℝ≥0 => X.X r ω) v - X.X v ω else 0
    let Y : ℝ≥0 → ℝ := fun t => X.X t ω + J t
    let z : ℕ → ℝ := fun i =>
      x + X.X (u i) ω - rightLimit D (u i) ω
    let c : ℕ → ℝ := fun i => Y (u (i + 1)) - Y (u i)
    ∀ ε : ℝ, 0 < ε →
      ∃ δ : ℝ, 0 < δ ∧
      (∀ i, i < n →
        Set.uIcc (z i) (z i + c i) ⊆ Set.Icc a b) →
      (∀ i, i < n → |c i| < δ) →
      (∀ i, i < n →
        IntervalIntegrable (deriv w) volume (z i) (z i + c i) ∧
        ∀ v ∈ Set.uIoc (z i) (z i + c i),
          |deriv w v - deriv w (z i)| ≤ ε)  := by
  intro J Y z c ε hε
  obtain ⟨δ, hδ, hMod⟩ :=
    avram_p3_f2_original_stopped_uniform_interior_C1_mesh_positive_delta
      X x C D hD w hwC1 hOpen a b hBand ω u n ε hε
  refine ⟨δ, ?_⟩
  intro hδSeg hSmall i hi
  exact hMod hδSeg.2 hSmall i hi
