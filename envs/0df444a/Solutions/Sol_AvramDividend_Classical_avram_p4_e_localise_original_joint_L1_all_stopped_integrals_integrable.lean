-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_all_stopped_integrals_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T15:00:56.059211+00:00
-- url     : https://prove2.me/submissions/888d0a11-b1cd-4efc-9c2d-8c29786db24b

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_clock_product_measurable_sets
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Joint L¹ makes every true ruin-clipped physical integral and the full ruin integral globally L¹. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hDiv : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P)) :
    Integrable (fun ω => ∫ t : ℝ≥0,
      if (t : ℝ≥0∞) < ruinTime X x D ω then f (t, ω) else 0 ∂μ) P ∧
    ∀ n : ℕ, Integrable (fun ω => ∫ t : ℝ≥0,
      if (t : ℝ≥0∞) < min (ruinTime X x D ω) (n : ℝ≥0∞)
      then f (t, ω) else 0 ∂μ) P := by
  have hSets :=
    avram_p4_e_localise_original_ruin_clock_product_measurable_sets
      X x D hDiv
  have hFullEq : (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) < ruinTime X x D p.2 then f p else 0) =
      ({p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) < ruinTime X x D p.2}).indicator f := by
    funext p
    by_cases hp : (p.1 : ℝ≥0∞) < ruinTime X x D p.2
    · simp [Set.indicator, hp]
    · simp [Set.indicator, hp]
  have hFull : Integrable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) < ruinTime X x D p.2 then f p else 0)
      (μ.prod P) := by
    rw [hFullEq]
    exact hf.indicator hSets.1
  refine ⟨hFull.integral_prod_right, ?_⟩
  intro n
  have hnEq : (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) < min (ruinTime X x D p.2) (n : ℝ≥0∞)
      then f p else 0) =
      ({p : ℝ≥0 × Ω | (p.1 : ℝ≥0∞) <
        min (ruinTime X x D p.2) (n : ℝ≥0∞)}).indicator f := by
    funext p
    classical
    simp only [Set.indicator, Set.mem_setOf_eq]
  have hn : Integrable (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) < min (ruinTime X x D p.2) (n : ℝ≥0∞)
      then f p else 0) (μ.prod P) := by
    rw [hnEq]
    exact hf.indicator (hSets.2 n)
  exact hn.integral_prod_right