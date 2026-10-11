-- Prove2me | solution 1 for ComparativeAdvantage.autarky_frontier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-10T18:53:48.720153+00:00
-- url     : https://prove2.me/submissions/0a155ea0-c73b-498a-a951-c9b2fe395667

import Mathlib
import Definitions.Def_ComparativeAdvantage_Model

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open ComparativeAdvantage

theorem solution (c : Country) :
    (∀ q ∈ autarkySet c, q.1 ≤ c.L / c.aLC - (c.aLW / c.aLC) * q.2) ∧
    ∀ QW : ℝ, 0 ≤ QW → QW ≤ c.L / c.aLW →
      (c.L / c.aLC - (c.aLW / c.aLC) * QW, QW) ∈ autarkySet c := by
  have hc : c.aLC ≠ 0 := ne_of_gt c.aLC_pos
  constructor
  · intro q hq
    rcases hq with ⟨hqc, hqw, hbudget⟩
    apply le_sub_iff_add_le.mpr
    apply (le_div_iff₀ c.aLC_pos).2
    have hrewrite :
        (q.1 + c.aLW / c.aLC * q.2) * c.aLC =
          c.aLC * q.1 + c.aLW * q.2 := by
      field_simp [hc] <;> ring
    rw [hrewrite]
    exact hbudget
  · intro QW hQW hmax
    have hW : c.aLW * QW ≤ c.L := by
      have hm := (le_div_iff₀ c.aLW_pos).1 hmax
      nlinarith
    have hQ : 0 ≤ c.L / c.aLC - c.aLW / c.aLC * QW := by
      apply sub_nonneg.mpr
      have hrewrite : c.aLW / c.aLC * QW =
          (c.aLW * QW) / c.aLC := by ring
      rw [hrewrite]
      apply (le_div_iff₀ c.aLC_pos).2
      have heq : (c.aLW * QW / c.aLC) * c.aLC =
          c.aLW * QW := by field_simp [hc]
      rw [heq]
      exact hW
    refine ⟨hQ, hQW, ?_⟩
    have hbudget :
        c.aLC * (c.L / c.aLC - c.aLW / c.aLC * QW) +
          c.aLW * QW = c.L := by
      field_simp [hc] <;> ring
    exact le_of_eq hbudget
