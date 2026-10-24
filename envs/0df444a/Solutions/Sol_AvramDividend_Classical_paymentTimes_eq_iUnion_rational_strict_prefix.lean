-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_eq_iUnion_rational_strict_prefix
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:01:25.529517+00:00
-- url     : https://prove2.me/submissions/0eac585b-1abd-4139-b0d3-80ba6ddffd80

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Positive pre-ruin payment times are exhausted by rational strict prefixes,
    including the possible initial dividend atom and an infinite ruin time. -/
theorem solution
    (σ : ℝ≥0∞) (hσ : 0 < σ) :
    paymentTimes σ =
      ⋃ q : {q : ℚ // 0 < ((q : ℚ) : ℝ) ∧
        ENNReal.ofReal ((q : ℚ) : ℝ) < σ},
          Ico (0 : ℝ) ((q : ℚ) : ℝ) := by
  ext t
  constructor
  · intro ht
    have ht0 : 0 ≤ t := ht.1
    have htσ : ENNReal.ofReal t < σ := by
      rcases ht.2 with hzero | hlt
      · simpa [hzero] using hσ
      · exact hlt
    by_cases htop : σ = ⊤
    · obtain ⟨r, htr⟩ := exists_rat_gt t
      have hr0 : 0 < (r : ℝ) := lt_of_le_of_lt ht0 htr
      have hrσ : ENNReal.ofReal (r : ℝ) < σ := by
        simp [htop]
      exact Set.mem_iUnion.mpr
        ⟨⟨r, ⟨hr0, hrσ⟩⟩, ⟨ht0, htr⟩⟩
    · have htR : t < σ.toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal ht0 htop).mp htσ
      obtain ⟨r, htr, hrR⟩ := exists_rat_btwn htR
      have hr0 : 0 < (r : ℝ) := lt_of_le_of_lt ht0 htr
      have hrσ : ENNReal.ofReal (r : ℝ) < σ :=
        (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hr0) htop).mpr hrR
      exact Set.mem_iUnion.mpr
        ⟨⟨r, ⟨hr0, hrσ⟩⟩, ⟨ht0, htr⟩⟩
  · intro ht
    obtain ⟨r, hr⟩ := Set.mem_iUnion.mp ht
    have ht0 : 0 ≤ t := hr.1
    have htr : t < ((r : ℚ) : ℝ) := hr.2
    have he : ENNReal.ofReal t ≤ ENNReal.ofReal ((r : ℚ) : ℝ) :=
      ENNReal.ofReal_le_ofReal (le_of_lt htr)
    exact ⟨ht0, Or.inr (lt_of_le_of_lt he r.property.2)⟩
