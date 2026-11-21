-- Prove2me | solution 1 for AvramDividend.Classical.avram_a35_original_zerojump_finitecap_fullband_positive_spatial_crossing_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:23:50.926525+00:00
-- url     : https://prove2.me/submissions/871af1f5-4d64-4450-8b35-24a9cb15d0e7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a34_original_finitecap_zero_contact_one_sided_caplinear_crossing
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_zerojump_actual_random_crossing_increment_ae_zero
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
import Theorems.Thm_AvramDividend_Classical_avram_ga_a108_true_gaussian_unique_crossing_positive_L1_dominated_convergence
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
    (hw0 : 0 ≤ w 0) (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc 0 c)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
         then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
         else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
         w (y m ω)) 0) P) :
    Tendsto (fun m => ∫ ω,
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
         then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
         else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
         w (y m ω)) 0 ∂P) atTop (nhds (0 : ℝ))  := by
  let V : ℝ → ℝ := fun z =>
    if z ≤ c then w z else w c + (z - c)
  let DX : ℕ → Ω → ℝ := fun m ω =>
    X.X (t m ω) ω - X.X (s m ω) ω
  let F : ℕ → Ω → ℝ := fun m ω =>
    V (y m ω + DX m ω) - w (y m ω)
  obtain ⟨K, hK, hL⟩ :=
    avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
      w c hc hwcont hwneg
  obtain ⟨B0, hB0I, hB0⟩ :=
    avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
      X hν T
  let B : Ω → ℝ := fun ω => K + c + B0 ω
  have hBI : Integrable B P := by
    dsimp [B]
    exact (integrable_const (K + c)).add hB0I
  have hB : ∀ᵐ ω ∂P, 0 ≤ B ω := by
    filter_upwards [hB0] with ω hb0
    dsimp [B]
    linarith [hb0.1]
  have hDom : ∀ᵐ ω ∂P, ∀ m, max (F m ω) 0 ≤ B ω := by
    filter_upwards [hy, hRange, hB0] with ω hY hRange0 hBound
    intro m
    have hbnd := hBound.2 (s m ω) (t m ω)
      (hRange0 m).1.2 (hRange0 m).2.2
    have hboundV := hL (y m ω) (DX m ω)
      (hY m).1 (hY m).2
    have hmax :
        max (F m ω) 0 ≤ |F m ω| := by
      exact max_le (le_abs_self _) (abs_nonneg _)
    have hZ : |DX m ω| ≤ B0 ω := by
      simpa only [DX] using hbnd
    have hFV : |F m ω| ≤ K + c + |DX m ω| := by
      simpa only [F, V] using hboundV
    change max (F m ω) 0 ≤ B ω
    dsimp [B]
    linarith
  have hDAE : ∀ᵐ ω ∂P, Tendsto
      (fun m => DX m ω) atTop (nhds (0 : ℝ)) := by
    simpa only [DX] using
      (avram_a27_original_zerojump_actual_random_crossing_increment_ae_zero
        X hν T s t hRange hGap)
  have hFAE : ∀ᵐ ω ∂P, Tendsto
      (fun m => max (F m ω) 0) atTop (nhds (0 : ℝ)) := by
    filter_upwards [hy, hDAE] with ω hY hD
    have ht :=
      avram_a34_original_finitecap_zero_contact_one_sided_caplinear_crossing
        w c hc hw0 hwneg hwcont
        (fun m => y m ω) (fun m => DX m ω) hY hD
    convert ht using 1
    funext m
    simp [F, V, (hY m).2]
  have hIntegral :=
    avram_ga_a108_true_gaussian_unique_crossing_positive_L1_dominated_convergence
      P (fun _ _ => ({0} : Finset ℕ))
      (fun m _ ω => F m ω) B hBI hB
      (Filter.Eventually.of_forall (fun ω m => by simp))
      (by filter_upwards [hDom] with ω hD
          intro m i hi
          simpa only [Finset.mem_singleton] using hD m)
      (by intro m
          simpa [F, V, DX] using hMeas m)
      (by filter_upwards [hFAE] with ω hF
          simpa only [Finset.sum_singleton] using hF)
  simpa [F, V, DX] using hIntegral
