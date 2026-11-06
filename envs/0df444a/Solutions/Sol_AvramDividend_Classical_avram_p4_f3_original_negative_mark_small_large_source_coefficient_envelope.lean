-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f3_original_negative_mark_small_large_source_coefficient_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:54:22.036384+00:00
-- url     : https://prove2.me/submissions/b0198726-fe6a-477b-98a8-63a152bec853

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_band_lipschitz_source
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_tail_global_value_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original value function's negative-jump coefficient has a source-exact small/large envelope. -/
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) :
    ∃ A B : ℝ, 0 ≤ A ∧
      ∀ u ∈ Icc δ K, ∀ z : ℝ, z < 0 →
        (-(δ / 2) < z →
          |w (u + z) - w u| ≤ B * |z|) ∧
        (z ≤ -(δ / 2) →
          |w (u + z) - w u| ≤ 2 * A) := by
  have hK0 : 0 ≤ K := le_trans (le_of_lt hδ) hδK
  obtain ⟨A, hA0, hA⟩ :=
    avram_p4_f3_original_negative_tail_global_value_bound
      w hw_cont hw_neg K hK0
  obtain ⟨B, hB⟩ :=
    avram_p4_f3_original_positive_band_lipschitz_source
      w C hw_smooth (δ / 2) K (by linarith) (by linarith) hK
  refine ⟨A, B, hA0, ?_⟩
  intro u hu z hz
  constructor
  · intro hzSmall
    have huHalf : u ∈ Icc (δ / 2) K :=
      ⟨by linarith [hu.1], hu.2⟩
    have huvHalf : u + z ∈ Icc (δ / 2) K :=
      ⟨by linarith [hu.1], by linarith [hu.2]⟩
    have h := hB u huHalf (u + z) huvHalf
    simpa only [show u + z - u = z by ring] using h
  · intro hzLarge
    have hFirst : |w (u + z)| ≤ A := hA (u + z) (by linarith [hu.2])
    have hSecond : |w u| ≤ A := hA u hu.2
    calc
      |w (u + z) - w u| ≤ |w (u + z)| + |w u| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          (abs_sub_le (w (u + z)) (0 : ℝ) (w u))
      _ ≤ A + A := add_le_add hFirst hSecond
      _ = 2 * A := by ring
