-- Prove2me | solution 1 for AvramDividend.Classical.avram_a36_original_zerojump_fullband_discounted_actual_crossing_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T16:36:53.995657+00:00
-- url     : https://prove2.me/submissions/391cf279-8465-4f7c-8fac-d53e2756f965

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a35_original_zerojump_finitecap_fullband_positive_spatial_crossing_L1
import Theorems.Thm_AvramDividend_Classical_avram_a34b_original_zerojump_fullband_true_crossing_uniform_integrable_majorant
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
    (hw0 : 0 ≤ w 0) (hwneg : ∀ z : ℝ, z < 0 → w z = 0)
    (hwcont : ContinuousOn w (Set.Ici 0))
    (y : ℕ → Ω → ℝ)
    (hy : ∀ᵐ ω ∂P, ∀ m, y m ω ∈ Set.Icc 0 c)
    (hMeas : ∀ m, AEStronglyMeasurable (fun ω =>
      max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
         then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
         else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
         w (y m ω)) 0) P)
    (q : ℝ) (hq : 0 ≤ q)
    (ρ : ℕ → Ω → ℝ≥0) (hρmeas : ∀ m, Measurable (ρ m)) :
    Tendsto (fun m => ∫ ω,
      Real.exp (-(q * (ρ m ω : ℝ))) * max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
         then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
         else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
         w (y m ω)) 0 ∂P) atTop (nhds (0 : ℝ))  := by
  let F : ℕ → Ω → ℝ := fun m ω =>
    max ((if y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) ≤ c
      then w (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω))
      else w c + (y m ω + (X.X (t m ω) ω - X.X (s m ω) ω) - c)) -
      w (y m ω)) 0
  let E : ℕ → Ω → ℝ := fun m ω =>
    Real.exp (-(q * (ρ m ω : ℝ)))
  obtain ⟨B, hBI, hB⟩ :=
    avram_a34b_original_zerojump_fullband_true_crossing_uniform_integrable_majorant
      X hν T s t hRange w c hc hwcont hwneg y hy
  have hFmeas : ∀ m, AEStronglyMeasurable (F m) P := by
    intro m
    simpa only [F] using hMeas m
  have hFI : ∀ m, Integrable (F m) P := by
    intro m
    have hDom : ∀ᵐ ω ∂P, ‖F m ω‖ ≤ B ω := by
      filter_upwards [hB] with ω hb
      have hFp : 0 ≤ F m ω := le_max_right _ _
      simpa only [Real.norm_eq_abs, abs_of_nonneg hFp] using hb.2 m
    exact Integrable.mono' hBI (hFmeas m) hDom
  have hFpos : ∀ m, ∀ᵐ ω ∂P, 0 ≤ F m ω := by
    intro m
    exact Filter.Eventually.of_forall
      (fun ω => le_max_right _ _)
  have hEm : ∀ m, AEStronglyMeasurable (E m) P := by
    intro m
    have hMe : Measurable (E m) := by
      dsimp [E]
      fun_prop (disch := assumption)
    exact hMe.aestronglyMeasurable
  have hEb : ∀ m, ∀ᵐ ω ∂P, 0 ≤ E m ω ∧ E m ω ≤ 1 := by
    intro m
    refine Filter.Eventually.of_forall (fun ω => ?_)
    dsimp [E]
    have hnonneg : 0 ≤ q * (ρ m ω : ℝ) :=
      mul_nonneg hq (by exact_mod_cast (bot_le : (0 : ℝ≥0) ≤ ρ m ω))
    constructor
    · exact le_of_lt (Real.exp_pos _)
    · rw [← Real.exp_zero]
      apply Real.exp_le_exp.mpr
      linarith
  have hLimit : Tendsto (fun m => ∫ ω, F m ω ∂P)
      atTop (nhds (0 : ℝ)) := by
    simpa only [F] using
      (avram_a35_original_zerojump_finitecap_fullband_positive_spatial_crossing_L1
        X hν T s t hRange hGap w c hc hw0 hwneg hwcont y hy hMeas)
  have ht := avram_a30_original_discount_weighted_nonnegative_L1_squeeze
    P F E hFI hFpos hEm hEb hLimit
  simpa only [E, F] using ht
