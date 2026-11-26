-- Prove2me | solution 1 for Eden.eventually_dimension_formula_of_neutral_prefix
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T14:19:49.226536+00:00
-- url     : https://prove2.me/submissions/1f200a5d-495e-491c-a10f-31f52d5c7575

import Definitions.Def_Eden_DimensionConvergence
import Definitions.Def_Eden_EventualDimensionFormulas
import Theorems.Thm_Eden_tendsto_spectrumPartialSum_normalized
import Theorems.Thm_Eden_kaplanYorkeIndex_eq_of_adjacent_signs
import Theorems.Thm_Eden_finiteTimeDimension_eq_kaplanYorke
import Theorems.Thm_Eden_kaplanYorkeDimension_formula_of_index_lt_five
import Theorems.Thm_Eden_normalizedLogSingularValues_antitone
import Theorems.Thm_Eden_spectrumEntry_at_kaplanYorkeIndex_neg
import Theorems.Thm_Eden_spectrumPartialSum_succ


set_option autoImplicit true
noncomputable section
open Set Filter
open scoped Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) (p : PhaseSpace)
    {k : ℕ} (hk : k < 5)
    (hlim₀ : ∀ i : Fin 5, i.val < k → lyapunovExponent c p i = 0)
    (hlim₁ : lyapunovExponent c p ⟨k, hk⟩ < 0)
    (hfinite : ∀ᶠ t in atTop, ∀ i : Fin 5, i.val < k →
      0 ≤ normalizedLogSingularValues c t p i) :
    ∀ᶠ t in atTop,
      (∀ i : Fin 5, i.val < k → 0 ≤ normalizedLogSingularValues c t p i) ∧
      spectrumPartialSum (normalizedLogSingularValues c t p) (k + 1) < 0 ∧
      normalizedLogSingularValues c t p ⟨k, hk⟩ < 0 ∧
      finiteTimeDimension c t p = (k : ℝ) +
        spectrumPartialSum (normalizedLogSingularValues c t p) k /
          -normalizedLogSingularValues c t p ⟨k, hk⟩ := by
  have hsum₀ : spectrumPartialSum (lyapunovExponent c p) k = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi₅ := lt_trans (Finset.mem_range.mp hi) hk
    rw [spectrumEntry, dif_pos hi₅, hlim₀ ⟨i, hi₅⟩ (Finset.mem_range.mp hi)]
  have hsum₁ : spectrumPartialSum (lyapunovExponent c p) (k + 1) < 0 := by
    rw [spectrumPartialSum_succ, hsum₀, zero_add, spectrumEntry, dif_pos hk]
    exact hlim₁
  have he := (tendsto_spectrumPartialSum_normalized c p (k + 1)).eventually
    (Iio_mem_nhds hsum₁)
  filter_upwards [he, hfinite, eventually_gt_atTop (0 : ℝ)] with t hnext hnonneg ht
  have hsum : 0 ≤ spectrumPartialSum (normalizedLogSingularValues c t p) k := by
    apply Finset.sum_nonneg
    intro i hi
    have hi₅ := lt_trans (Finset.mem_range.mp hi) hk
    rw [spectrumEntry, dif_pos hi₅]
    exact hnonneg ⟨i, hi₅⟩ (Finset.mem_range.mp hi)
  have hindex := kaplanYorkeIndex_eq_of_adjacent_signs
    (normalizedLogSingularValues_antitone c ht p) hk hsum hnext
  have hj : kaplanYorkeIndex (normalizedLogSingularValues c t p) < 5 := by
    rw [hindex]; exact hk
  have hneg := spectrumEntry_at_kaplanYorkeIndex_neg hj
  rw [hindex, spectrumEntry, dif_pos hk] at hneg
  refine ⟨hnonneg, hnext, hneg, ?_⟩
  rw [finiteTimeDimension_eq_kaplanYorke c ht p,
    kaplanYorkeDimension_formula_of_index_lt_five hj, hindex, spectrumEntry, dif_pos hk]
end Eden
