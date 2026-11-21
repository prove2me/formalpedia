-- Prove2me | solution 1 for AvramDividend.Classical.avram_a29_original_finitecap_actual_gaussian_crossing_expected_L1_automatic_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:27:11.487774+00:00
-- url     : https://prove2.me/submissions/702dd0bb-66e7-40b8-80c1-70a37438cce0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_gaussian_finiteprob_horizon_increment_L1_majorant
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_zerojump_finitecap_actual_random_crossing_positive_L1
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
       w (y m ω)) 0) P) :
    Tendsto (fun m => ∫ ω,
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0 ∂P)
       atTop (nhds (0 : ℝ))  := by
  obtain ⟨B₀, hBI₀, hBall⟩ :=
    avram_a28_original_gaussian_finiteprob_horizon_increment_L1_majorant X hν T
  obtain ⟨K, hK, hKbound⟩ :=
    avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
      w c hc hw_cont hw_neg
  let V : ℝ → ℝ := fun z => if z ≤ c then w z else w c + (z - c)
  let δ : ℕ → Ω → ℝ := fun m ω => X.X (t m ω) ω - X.X (s m ω) ω
  let B : Ω → ℝ := fun ω => K + c + B₀ ω
  have hBInt : Integrable B P :=
    (integrable_const (K + c)).add hBI₀
  have hYcap : ∀ᵐ ω ∂P, ∀ m, y m ω ≤ c := by
    filter_upwards [hy] with ω hyω m
    exact (hyω m).2.trans hbc
  have hBpos : ∀ᵐ ω ∂P, 0 ≤ B ω := by
    filter_upwards [hBall] with ω hω
    dsimp [B]
    linarith [hω.1]
  have hDom : ∀ m, ∀ᵐ ω ∂P,
      max (V (y m ω + δ m ω) - V (y m ω)) 0 ≤ B ω := by
    intro m
    filter_upwards [hy, hRange, hBall] with ω hyω hTω hBω
    have hYm := hyω m
    have hYc : y m ω ≤ c := hYm.2.trans hbc
    have hY0 : 0 ≤ y m ω := by linarith [hYm.1, hra, hr]
    have hCell := hKbound (y m ω) (δ m ω) hY0 hYc
    have hΔ := hBω.2 (s m ω) (t m ω) (hTω m).1.2 (hTω m).2.2
    have hPos : max (V (y m ω + δ m ω) - V (y m ω)) 0 ≤
        |(if y m ω + δ m ω ≤ c then w (y m ω + δ m ω)
          else w c + (y m ω + δ m ω - c)) - w (y m ω)| := by
      simpa [V, hYc] using
        (max_le (le_abs_self ((if y m ω + δ m ω ≤ c
          then w (y m ω + δ m ω)
          else w c + (y m ω + δ m ω - c)) - w (y m ω)))
          (abs_nonneg _))
    dsimp [δ] at hPos
    dsimp [δ] at hCell
    dsimp [B]
    linarith
  have hMeasV : ∀ m, AEStronglyMeasurable (fun ω =>
      max (V (y m ω + δ m ω) - V (y m ω)) 0) P := by
    intro m
    apply (hMeas m).congr
    filter_upwards [hYcap] with ω hcap
    simp [V, δ, hcap m]
  have ht := avram_a27_original_zerojump_finitecap_actual_random_crossing_positive_L1
    X hν T s t hRange hGap w c hc hw_cont a b r hr hra hab y hy
    B hBInt hBpos (by intro m; simpa [V, δ] using hDom m)
    (by intro m; simpa [V, δ] using hMeasV m)
  convert ht using 1
  funext m
  apply integral_congr_ae
  filter_upwards [hYcap] with ω hcap
  simp [V, δ, hcap m]
