-- Prove2me | solution 1 for AvramDividend.Classical.avram_a40_original_actual_stop_uniform_discounted_gaussian_crossing_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:42:47.383934+00:00
-- url     : https://prove2.me/submissions/2cd79910-26e8-4de5-8c77-6bdbb5edc1fd

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a38_original_true_stop_crossing_uniform_grid_clock_gap
import Theorems.Thm_AvramDividend_Classical_avram_a36_original_zerojump_fullband_discounted_actual_crossing_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρ : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (i : ℕ → Ω → ℕ)
    (hCell : ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i m ω : ℝ≥0) * Δ ≤ ρ ω ∧
        ρ ω ≤ (i m ω : ℝ≥0) * Δ + Δ)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw0 : 0 ≤ w 0) (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc 0 c)
    (hMeas : ∀ (m : ℕ), AEStronglyMeasurable (fun ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      max ((if y m ω + (X.X (ρ ω) ω - X.X s ω) ≤ c
        then w (y m ω + (X.X (ρ ω) ω - X.X s ω))
        else w c + (y m ω + (X.X (ρ ω) ω - X.X s ω) - c)) -
        w (y m ω)) 0) P)
    (q : ℝ) (hq : 0 ≤ q)
    (hρmeas : Measurable ρ) :
    Tendsto (fun (m : ℕ) => ∫ ω,
      Real.exp (-(q * (ρ ω : ℝ))) *
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i m ω : ℝ≥0) * Δ
      max ((if y m ω + (X.X (ρ ω) ω - X.X s ω) ≤ c
        then w (y m ω + (X.X (ρ ω) ω - X.X s ω))
        else w c + (y m ω + (X.X (ρ ω) ω - X.X s ω) - c)) -
        w (y m ω)) 0 ∂P) atTop (nhds (0 : ℝ))  := by
  let s : ℕ → Ω → ℝ≥0 := fun m ω =>
    (i m ω : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))
  let t : ℕ → Ω → ℝ≥0 := fun _ ω => ρ ω
  have hGrid :=
    avram_a38_original_true_stop_crossing_uniform_grid_clock_gap
      n ρ hρ i hCell
  have hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Icc 0 (n : ℝ≥0) ∧
      t m ω ∈ Icc 0 (n : ℝ≥0) := by
    exact Filter.Eventually.of_forall (fun ω m =>
      ⟨(hGrid m ω).1, (hGrid m ω).2.1⟩)
  have hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤
        (n : ℝ≥0) / ((m : ℝ≥0) + 1) := by
    exact Filter.Eventually.of_forall (fun ω m =>
      (hGrid m ω).2.2)
  have hMeas' (m : ℕ) : AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
        then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
        else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
        w (y m ω)) 0) P := by
    simpa [s, t] using hMeas m
  have ht :=
    avram_a36_original_zerojump_fullband_discounted_actual_crossing_L1
      X hν (n : ℝ≥0) s t hRange hGap
      w c hc hw0 hwneg hwcont y hy hMeas' q hq
      (fun _ => ρ) (fun _ => hρmeas)
  simpa [s, t] using ht
