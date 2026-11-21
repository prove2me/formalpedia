-- Prove2me | solution 1 for AvramDividend.Classical.avram_a31_original_finitecap_actual_gaussian_spatial_positive_mesh_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:38:30.634657+00:00
-- url     : https://prove2.me/submissions/6d569d91-a9ef-4f0b-a2f7-641b9405d1a4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
import Theorems.Thm_AvramDividend_Classical_avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hRange : ∀ᵐ ω ∂P, ∀ m,
      s m ω ≤ T ∧ t m ω ≤ T)
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_cont : ContinuousOn w (Set.Ici 0))
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, 0 ≤ y m ω ∧ y m ω ≤ c)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0) P) :
    ∀ m, Integrable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
       then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
       else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
       w (y m ω)) 0) P  := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨B₀, hBI₀, hBall⟩ :=
    avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant X hν T
  obtain ⟨K, hK, hKbound⟩ :=
    avram_a25_original_finitecap_gaussian_crossing_value_difference_linear_envelope
      w c hc hw_cont hw_neg
  have hEnv : Integrable (fun ω => K + c + B₀ ω) P :=
    (integrable_const (K + c)).add hBI₀
  intro m
  refine hEnv.mono' (hMeas m) ?_
  filter_upwards [hRange, hy, hBall] with ω hT hY hB
  let δ : ℝ := X.X (t m ω) ω - X.X (s m ω) ω
  let z : ℝ := (if y m ω + δ ≤ c then w (y m ω + δ)
     else w c + (y m ω + δ - c)) - w (y m ω)
  have hBounds := hY m
  have hScalar : |z| ≤ K + c + |δ| := by
    simpa only [z, δ] using
      (hKbound (y m ω) δ hBounds.1 hBounds.2)
  have hIncr : |δ| ≤ B₀ ω :=
    hB.2 (s m ω) (t m ω) (hT m).1 (hT m).2
  have hPos : 0 ≤ max z 0 := le_max_right _ _
  have hMaxAbs : max z 0 ≤ |z| :=
    max_le (le_abs_self _) (abs_nonneg _)
  have hUp : ‖max z 0‖ ≤ K + c + B₀ ω := by
    rw [Real.norm_eq_abs, abs_of_nonneg hPos]
    linarith
  simpa only [z, δ] using hUp
