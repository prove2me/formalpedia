-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_eq_zero_union_Ioc_of_cofinal_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T17:05:59.885065+00:00
-- url     : https://prove2.me/submissions/79c9bb3c-47af-470a-bec5-a7d7f0829870

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-- Strict pre-ruin payments decompose into the initial point and any
countably cofinal family of open-left, closed-right time prefixes. -/
theorem solution
    (σ : ℝ≥0∞) (grid : ℕ → ℝ≥0)
    (hbelow : ∀ n : ℕ, (grid n : ℝ≥0∞) < σ)
    (hcofinal : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ)) :
    paymentTimes σ =
      {(0 : ℝ)} ∪ ⋃ n : ℕ, Ioc (0 : ℝ) (grid n : ℝ) := by
  ext t
  simp only [paymentTimes, Set.mem_union, Set.mem_singleton_iff,
    Set.mem_iUnion, Set.mem_Ioc, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hnonneg, hzero | hbefore⟩
    · exact Or.inl hzero
    · by_cases hzero : t = 0
      · exact Or.inl hzero
      · have htpos : 0 < t := lt_of_le_of_ne hnonneg (Ne.symm hzero)
        obtain ⟨n, hle⟩ := hcofinal t htpos hbefore
        exact Or.inr ⟨n, htpos, hle⟩
  · rintro (hzero | ⟨n, htpos, hle⟩)
    · exact ⟨le_of_eq hzero.symm, Or.inl hzero⟩
    · have hmono : ENNReal.ofReal t ≤ ENNReal.ofReal (grid n : ℝ) :=
        ENNReal.ofReal_le_ofReal hle
      have hgrid : ENNReal.ofReal (grid n : ℝ) < σ := by
        simpa only [ENNReal.ofReal_coe_nnreal] using hbelow n
      exact ⟨le_of_lt htpos, Or.inr (hmono.trans_lt hgrid)⟩
