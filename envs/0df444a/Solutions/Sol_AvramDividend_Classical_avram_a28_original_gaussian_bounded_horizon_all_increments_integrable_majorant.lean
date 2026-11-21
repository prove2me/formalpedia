-- Prove2me | solution 1 for AvramDividend.Classical.avram_a28_original_gaussian_bounded_horizon_all_increments_integrable_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:26:55.86918+00:00
-- url     : https://prove2.me/submissions/51ac8d94-27b1-4478-ac20-e33e08bcd556

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (T : ℝ≥0) :
    ∃ B : Ω → ℝ, Integrable B P ∧
      (∀ᵐ ω ∂P, 0 ≤ B ω ∧
        ∀ s t : ℝ≥0, s ≤ T → t ≤ T →
          |X.X t ω - X.X s ω| ≤ B ω)  := by
  letI : IsProbabilityMeasure P := X.isProbability
  obtain ⟨S, hSI, hS⟩ :=
    avram_ga_a400_zerojump_centred_source_horizon_sup_square_integrable X hν T
  let B : Ω → ℝ := fun ω => 2 + 2 * S ω + (T : ℝ) * |X.c|
  have hBI : Integrable B P := by
    exact ((integrable_const 2).add (hSI.const_mul 2)).add
      (integrable_const ((T : ℝ) * |X.c|))
  refine ⟨B, hBI, ?_⟩
  filter_upwards [hS] with ω hSω
  obtain ⟨hS0, hSq⟩ := hSω
  constructor
  · dsimp [B]
    positivity
  · intro s t hs ht
    let A : ℝ := X.X t ω - (t : ℝ) * X.c
    let C : ℝ := X.X s ω - (s : ℝ) * X.c
    have hA2 : A ^ 2 ≤ S ω := hSq t ht
    have hC2 : C ^ 2 ≤ S ω := hSq s hs
    have hA : |A| ≤ 1 + S ω := by
      have hPos := sq_nonneg (|A| - 1)
      nlinarith [sq_abs A]
    have hC : |C| ≤ 1 + S ω := by
      have hPos := sq_nonneg (|C| - 1)
      nlinarith [sq_abs C]
    have hs0 : 0 ≤ (s : ℝ) := by exact_mod_cast (show (0 : ℝ≥0) ≤ s from bot_le)
    have ht0 : 0 ≤ (t : ℝ) := by exact_mod_cast (show (0 : ℝ≥0) ≤ t from bot_le)
    have hsT : (s : ℝ) ≤ (T : ℝ) := by exact_mod_cast hs
    have htT : (t : ℝ) ≤ (T : ℝ) := by exact_mod_cast ht
    have htime : |(t : ℝ) - (s : ℝ)| ≤ (T : ℝ) :=
      abs_le.mpr ⟨by linarith, by linarith⟩
    have hmul :
        |((t : ℝ) - (s : ℝ)) * X.c| ≤ (T : ℝ) * |X.c| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right htime (abs_nonneg _)
    have hEq : X.X t ω - X.X s ω =
        (A - C) + (((t : ℝ) - (s : ℝ)) * X.c) := by
      dsimp [A,C]
      ring
    have htri : |X.X t ω - X.X s ω| ≤
        |A| + |C| + |((t : ℝ) - (s : ℝ)) * X.c| := by
      rw [hEq]
      calc
        _ ≤ |A - C| + |((t : ℝ) - (s : ℝ)) * X.c| :=
          abs_add_le _ _
        _ ≤ (|A| + |C|) + |((t : ℝ) - (s : ℝ)) * X.c| := by
          have hSub : |A - C| ≤ |A| + |C| := by
            calc
              |A - C| = |A + (-C)| := by ring
              _ ≤ |A| + |-C| := abs_add_le _ _
              _ = |A| + |C| := by simp
          linarith
    dsimp [B]
    linarith
