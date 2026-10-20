-- Prove2me | solution 1 for AvramDividend.Classical.paymentTimes_eq_iUnion_strict_rational_prefixes
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T13:55:29.486232+00:00
-- url     : https://prove2.me/submissions/4d801c7a-dae5-4c9a-a950-a990e86b0085

import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (σ : ℝ≥0∞) (hσ : 0 < σ) :
    paymentTimes σ =
      ⋃ q : {q : ℚ // 0 < (q : ℝ) ∧ ENNReal.ofReal (q : ℝ) < σ},
        Ico (0 : ℝ) (q.val : ℝ) := by
  ext t
  simp only [paymentTimes, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_Ico]
  constructor
  · rintro ⟨htnonneg, hmem⟩
    have htσ : ENNReal.ofReal t < σ := by
      rcases hmem with ht0 | htlt
      · subst t
        simpa using hσ
      · exact htlt
    by_cases htop : σ = ⊤
    · obtain ⟨q, htq⟩ := exists_rat_gt t
      have hqpos : 0 < (q : ℝ) := lt_of_le_of_lt htnonneg htq
      have hqσ : ENNReal.ofReal (q : ℝ) < σ := by
        simp [htop]
      exact ⟨⟨q, ⟨hqpos, hqσ⟩⟩, htnonneg, htq⟩
    · have htToReal : t < σ.toReal :=
        (ENNReal.ofReal_lt_iff_lt_toReal htnonneg htop).mp htσ
      obtain ⟨q, htq, hqσreal⟩ := exists_rat_btwn htToReal
      have hqpos : 0 < (q : ℝ) := lt_of_le_of_lt htnonneg htq
      have hqσ : ENNReal.ofReal (q : ℝ) < σ :=
        (ENNReal.ofReal_lt_iff_lt_toReal (le_of_lt hqpos) htop).mpr hqσreal
      exact ⟨⟨q, ⟨hqpos, hqσ⟩⟩, htnonneg, htq⟩
  · rintro ⟨q, ht0, htq⟩
    refine ⟨ht0, Or.inr ?_⟩
    have hle : ENNReal.ofReal t ≤ ENNReal.ofReal (q.val : ℝ) :=
      ENNReal.ofReal_le_ofReal (le_of_lt htq)
    exact lt_of_le_of_lt hle q.property.2
