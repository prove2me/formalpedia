-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_eq_zero_union_filtered_Ioc_of_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:05:54.673994+00:00
-- url     : https://prove2.me/submissions/baa8ca78-17e4-48ac-b004-f5822d1e8ba1

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- A strict stopped payment set is the initial atom plus the union of
positive Stieltjes prefixes whose deterministic endpoints survive. -/
theorem solution
    (σ : ℝ≥0∞) (grid : ℕ → ℝ≥0)
    (hcofinal : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ) :
    paymentTimes σ =
      {(0 : ℝ)} ∪ ⋃ n : ℕ,
        {t : ℝ | 0 < t ∧ t ≤ (grid n : ℝ) ∧ (grid n : ℝ≥0∞) < σ} := by
  ext t
  simp only [paymentTimes, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_iUnion, Set.mem_Ioc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnonneg, hzero | hbefore⟩
    · exact Or.inl hzero
    · by_cases hzero : t = 0
      · exact Or.inl hzero
      · have htpos : 0 < t := lt_of_le_of_ne hnonneg (Ne.symm hzero)
        obtain ⟨n, hle, hsurv⟩ := hcofinal t htpos hbefore
        exact Or.inr ⟨n, htpos, hle, hsurv⟩
  · rintro (hzero | ⟨n, htpos, hle, hsurv⟩)
    · exact ⟨le_of_eq hzero.symm, Or.inl hzero⟩
    · have hmono : ENNReal.ofReal t ≤ ENNReal.ofReal (grid n : ℝ) :=
        ENNReal.ofReal_le_ofReal hle
      have hgrid : ENNReal.ofReal (grid n : ℝ) < σ := by
        simpa only [ENNReal.ofReal_coe_nnreal] using hsurv
      exact ⟨le_of_lt htpos, Or.inr (hmono.trans_lt hgrid)⟩
