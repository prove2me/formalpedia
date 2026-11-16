-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_finite_jump_drift_deficit_telescope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:57:15.732196+00:00
-- url     : https://prove2.me/submissions/8cd6298e-8725-48b3-afd8-3c687eddf052

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Theorems.Thm_AvramDividend_Classical_avram_bv_finite_jump_finset_drift_deficit_telescope
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (drift : ℝ) (T : ℝ≥0)
    (h0 : f 0 = 0)
    (hFinite : Set.Finite {t : ℝ≥0 |
      0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0})
    (hFlat : ∀ s t : ℝ≥0, s ≤ t → t ≤ T →
      (∀ u ∈ Set.Ioc s t, f u - Function.leftLim f u = 0) →
      (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    (∑' t : ℝ≥0, if 0 < t ∧ t ≤ T then
      Function.leftLim f t - f t else 0) =
      (T : ℝ) * drift - f T := by
  classical
  have hsupp (t : ℝ≥0) (ht : t ∉ hFinite.toFinset) :
      (if 0 < t ∧ t ≤ T then Function.leftLim f t - f t else 0) = 0 := by
    by_cases htime : 0 < t ∧ t ≤ T
    · have hz : f t - Function.leftLim f t = 0 := by
        by_contra hn
        exact ht (hFinite.mem_toFinset.mpr ⟨htime.1, htime.2, hn⟩)
      simp [htime, sub_eq_zero.mp hz]
    · simp [htime]
  have htsum :
      (∑' t : ℝ≥0, if 0 < t ∧ t ≤ T then
        Function.leftLim f t - f t else 0) =
      Finset.sum hFinite.toFinset
        (fun t => if 0 < t ∧ t ≤ T then Function.leftLim f t - f t else 0) := by
    apply tsum_eq_sum
    exact hsupp
  have hfin :
      Finset.sum hFinite.toFinset
        (fun t => if 0 < t ∧ t ≤ T then Function.leftLim f t - f t else 0) =
      Finset.sum hFinite.toFinset (fun t => Function.leftLim f t - f t) := by
    apply Finset.sum_congr rfl
    intro t ht
    have hm : 0 < t ∧ t ≤ T ∧ f t - Function.leftLim f t ≠ 0 :=
      hFinite.mem_toFinset.mp ht
    simp [hm.1, hm.2.1]
  exact htsum.trans (hfin.trans
    (avram_bv_finite_jump_finset_drift_deficit_telescope
      f drift T h0 hFinite hFlat))
