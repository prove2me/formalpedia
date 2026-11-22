-- Prove2me | solution 1 for AvramDividend.Classical.avram_freshD_original_true_finite_mark_times_grid_prestates_Taylor_upperlim
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T09:13:57.799344+00:00
-- url     : https://prove2.me/submissions/6e222c8a-e587-4b99-ae54-7d5ef621f3c0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_allactivity_postright_reserve_prejump_leftLimit_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_freshD_original_finitely_indexed_negative_marks_distinct_prestates_signed_upperlim
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (c : ℝ) (hc : 0 < c)
    (hcC : ENNReal.ofReal c ≤ C)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici (0 : ℝ)))
    (hwneg : ∀ y : ℝ, y < 0 → w y = 0)
    (S : Finset ℝ≥0)
    (hSpos : ∀ t ∈ S, 0 < t)
    (hSneg : ∀ t ∈ S,
      X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t < 0)
    (hSinterior : ∀ t ∈ S,
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω ∈
        Ioo (0 : ℝ) c)
    (grid : ℕ → ℝ≥0 → ℝ≥0)
    (hgrid : ∀ t ∈ S, Tendsto (fun m => grid m t) atTop (𝓝[<] t)) :
    let y : ℝ≥0 → ℝ := fun t =>
      x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω
    let z : ℝ≥0 → ℝ := fun t =>
      X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
    let u : ℕ → ℝ≥0 → ℝ := fun m t =>
      x + X.X (grid m t) ω - rightLimit D (grid m t) ω
    Tendsto
      (fun m => max
        (∑ t ∈ S,
          ((w (u m t + z t) - w (u m t) -
              (if -1 < z t then z t * deriv w (u m t) else 0)) -
           (w (y t + z t) - w (y t) -
              (if -1 < z t then z t * deriv w (y t) else 0)))) 0)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  dsimp only
  let y : ℝ≥0 → ℝ := fun t =>
    x + Function.leftLim (fun r : ℝ≥0 => X.X r ω) t - D t ω
  let z : ℝ≥0 → ℝ := fun t =>
    X.X t ω - Function.leftLim (fun r : ℝ≥0 => X.X r ω) t
  let u : ℕ → ℝ≥0 → ℝ := fun m t =>
    x + X.X (grid m t) ω - rightLimit D (grid m t) ω
  have hU : ∀ t ∈ S, Tendsto (fun m => u m t) atTop (𝓝 (y t)) := by
    intro t ht
    have hleft :=
      avram_freshD_original_allactivity_postright_reserve_prejump_leftLimit_tendsto
        X x D hD ω t (hSpos t ht)
    exact hleft.comp (hgrid t ht)
  have h := avram_freshD_original_finitely_indexed_negative_marks_distinct_prestates_signed_upperlim
    w C c hc hcC hw_smooth hw0 hwcont hwneg S z y
    (fun t ht => hSneg t ht)
    (fun t ht => hSinterior t ht) u hU
  simpa only [u, y, z] using h
