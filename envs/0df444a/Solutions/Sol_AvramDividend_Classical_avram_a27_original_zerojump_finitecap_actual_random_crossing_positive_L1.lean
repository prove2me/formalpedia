-- Prove2me | solution 1 for AvramDividend.Classical.avram_a27_original_zerojump_finitecap_actual_random_crossing_positive_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:21:43.180545+00:00
-- url     : https://prove2.me/submissions/ac87c6ac-b44f-411d-8b08-4e2e19cbd30b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_zerojump_actual_random_crossing_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_a26_original_finitecap_localised_gaussian_crossing_positive_expected_L1
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a) (hab : a ≤ b)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc a b)
    (B : Ω → ℝ) (hBI : Integrable B P)
    (hB : ∀ᵐ ω ∂P, 0 ≤ B ω)
    (hDom : ∀ m, ∀ᵐ ω ∂P,
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0 ≤ B ω)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0) P) :
    Tendsto (fun m => ∫ ω,
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       (if y m ω ≤ c then w (y m ω)
       else w c + (y m ω - c))) 0 ∂P)
       atTop (nhds (0 : ℝ))  := by
  let δ : ℕ → Ω → ℝ := fun m ω =>
    X.X (t m ω) ω - X.X (s m ω) ω
  have hδ : ∀ᵐ ω ∂P,
      Tendsto (fun m => δ m ω) atTop (nhds (0 : ℝ)) := by
    simpa only [δ] using
      (avram_a27_original_zerojump_actual_random_crossing_increment_ae_zero
        X hν T s t hRange hGap)
  have ht :=
    avram_a26_original_finitecap_localised_gaussian_crossing_positive_expected_L1
      P w c hc hw_cont a b r hr hra hab y δ hy hδ B hBI hB
      hDom hMeas
  simpa only [δ] using ht
