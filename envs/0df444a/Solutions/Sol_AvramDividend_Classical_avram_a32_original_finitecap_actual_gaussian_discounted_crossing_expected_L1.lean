-- Prove2me | solution 1 for AvramDividend.Classical.avram_a32_original_finitecap_actual_gaussian_discounted_crossing_expected_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:38:57.291512+00:00
-- url     : https://prove2.me/submissions/a71e1a60-61df-48de-ba79-ee4561d975fa

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a31_original_finitecap_actual_gaussian_spatial_positive_mesh_integrable
import Theorems.Thm_AvramDividend_Classical_avram_a29_original_finitecap_actual_gaussian_crossing_expected_L1_automatic_envelope
import Theorems.Thm_AvramDividend_Classical_avram_a30_original_discount_weighted_nonnegative_L1_squeeze
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ∈ Set.Icc 0 T ∧ t m ω ∈ Set.Icc 0 T)
    (hGap : ∀ᵐ ω ∂P, ∀ m,
      dist (s m ω) (t m ω) ≤ T / ((m : ℝ≥0) + 1))
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (a b r : ℝ) (hr : 0 < r) (hra : r ≤ a)
    (hab : a ≤ b) (hbc : b ≤ c)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc a b)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0) P)    (E : ℕ → Ω → ℝ)
    (hEm : ∀ m, AEStronglyMeasurable (E m) P)
    (hEb : ∀ m, ∀ᵐ ω ∂P, 0 ≤ E m ω ∧ E m ω ≤ 1) :
    Tendsto (fun m => ∫ ω,
      E m ω * max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0 ∂P)
       atTop (nhds (0 : ℝ))  := by
  letI : IsProbabilityMeasure P := X.isProbability
  let F : ℕ → Ω → ℝ := fun m ω =>
    max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
      then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
      else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
      w (y m ω)) 0
  have hT : ∀ᵐ ω ∂P, ∀ m,
      s m ω ≤ T ∧ t m ω ≤ T := by
    filter_upwards [hRange] with ω hr m
    exact ⟨(hr m).1.2, (hr m).2.2⟩
  have hY : ∀ᵐ ω ∂P, ∀ m,
      0 ≤ y m ω ∧ y m ω ≤ c := by
    filter_upwards [hy] with ω hyω m
    exact ⟨by linarith [(hyω m).1, hra, hr],
      (hyω m).2.trans hbc⟩
  have hFI : ∀ m, Integrable (F m) P := by
    simpa only [F] using
      (avram_a31_original_finitecap_actual_gaussian_spatial_positive_mesh_integrable
        X hν T s t hT w c hc hw_cont hw_neg y hY hMeas)
  have hFpos : ∀ m, ∀ᵐ ω ∂P, 0 ≤ F m ω := by
    intro m
    exact Filter.Eventually.of_forall (fun ω => le_max_right _ _)
  have hL : Tendsto (fun m => ∫ ω, F m ω ∂P)
      atTop (nhds (0 : ℝ)) := by
    simpa only [F] using
      (avram_a29_original_finitecap_actual_gaussian_crossing_expected_L1_automatic_envelope
        X hν T s t hRange hGap w c hc hw_cont hw_neg
        a b r hr hra hab hbc y hy hMeas)
  have hWeighted :=
    avram_a30_original_discount_weighted_nonnegative_L1_squeeze
      P F E hFI hFpos hEm hEb hL
  simpa only [F] using hWeighted
