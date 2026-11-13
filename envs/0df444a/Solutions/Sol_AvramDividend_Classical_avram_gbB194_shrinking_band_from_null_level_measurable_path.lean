-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB194_shrinking_band_from_null_level_measurable_path
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T22:19:03.395195+00:00
-- url     : https://prove2.me/submissions/94e7b6f4-2d48-4c3c-a5c5-bced82eaf06a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (f : ℝ → ℝ) (hf : Measurable f) (n : ℕ) (ρ b : ℝ)
    (hlevel : volume {t : ℝ |
      0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = b} = 0) :
    Tendsto (fun k : ℕ =>
      volume {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
        abs (f t - b) < (1 : ℝ) / ((k : ℝ) + 1)})
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let A : ℕ → Set ℝ := fun k =>
    {t | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧
      abs (f t - b) < (1 : ℝ) / ((k : ℝ) + 1)}
  have hA : ∀ k, MeasurableSet (A k) := by
    intro k
    have hAbs : Measurable (fun t : ℝ => abs (f t - b)) :=
      (hf.sub_const b).abs
    change MeasurableSet
      (Ioi 0 ∩ (Iio (n : ℝ) ∩ (Iio ρ ∩
        (fun t => abs (f t - b)) ⁻¹'
          Iio ((1 : ℝ) / ((k : ℝ) + 1)))))
    exact measurableSet_Ioi.inter (measurableSet_Iio.inter
      (measurableSet_Iio.inter (hAbs measurableSet_Iio)))
  have hanti : Antitone A := by
    intro i j hij t ht
    refine ⟨ht.1, ht.2.1, ht.2.2.1, lt_of_lt_of_le ht.2.2.2 ?_⟩
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (Nat.add_le_add_right hij 1)
  have hsub : (⋂ k, A k) ⊆
      {t : ℝ | 0 < t ∧ t < (n : ℝ) ∧ t < ρ ∧ f t = b} := by
    intro t ht
    obtain ⟨ht0, htn, htρ, _⟩ := (Set.mem_iInter.mp ht 0)
    refine ⟨ht0, htn, htρ, ?_⟩
    by_contra hne
    obtain ⟨k, hk⟩ :=
      exists_nat_one_div_lt (abs_pos.mpr (sub_ne_zero.mpr hne))
    exact (lt_asymm (Set.mem_iInter.mp ht k).2.2.2 hk)
  have hinter0 : volume (⋂ k, A k) = 0 :=
    le_antisymm ((measure_mono hsub).trans_eq hlevel) bot_le
  have hfinite : volume (A 0) ≠ (⊤ : ℝ≥0∞) := by
    have hle : volume (A 0) ≤ volume (Ioo (0 : ℝ) (n : ℝ)) :=
      measure_mono (fun t ht => ⟨ht.1, ht.2.1⟩)
    exact ne_of_lt (lt_of_le_of_lt hle (by simp [Real.volume_Ioo]))
  have hlim := MeasureTheory.tendsto_measure_iInter_atTop
    (μ := volume) (s := A)
    (fun k => (hA k).nullMeasurableSet) hanti ⟨0, hfinite⟩
  simpa only [Function.comp_def, hinter0, A] using hlim
