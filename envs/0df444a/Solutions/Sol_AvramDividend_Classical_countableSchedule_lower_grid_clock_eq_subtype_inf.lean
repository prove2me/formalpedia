-- Prove2me | solution 1 for AvramDividend.Classical.countableSchedule_lower_grid_clock_eq_subtype_inf
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-25T19:52:50.511057+00:00
-- url     : https://prove2.me/submissions/5594f65c-bf08-47e5-8685-2832b3a12d4c

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff
import Theorems.Thm_AvramDividend_Classical_inverseNatural_positive_grid_point_has_nat_schedule_index

open scoped NNReal ENNReal
open AvramDividend.Classical
theorem solution
    (g : ℝ≥0 → ℝ) (lower : ℝ) :
    (⨅ j : ℕ, if
          g (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) < lower
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) =
    (⨅ i : {p : ℕ × ℕ // 0 < p.1 ∧
          g ((p.2 : ℝ≥0) * (p.1 : ℝ≥0)⁻¹) < lower},
      (((i.1.2 : ℝ≥0) * (i.1.1 : ℝ≥0)⁻¹) : ℝ≥0∞)) := by
  apply AvramDividend.Classical.firstPassage_iInf_eq_of_strict_horizon_witness_iff
  intro T
  constructor
  · rintro ⟨j, hj⟩
    split_ifs at hj with hc
    · exact ⟨⟨((Nat.unpair j).1 + 1, (Nat.unpair j).2), Nat.succ_pos _, hc⟩, hj⟩
    · exact absurd hj (not_lt.2 le_top)
  · rintro ⟨⟨⟨n, k⟩, hn, hc⟩, hT⟩
    obtain ⟨j, hj⟩ := AvramDividend.Classical.inverseNatural_positive_grid_point_has_nat_schedule_index n k hn
    refine ⟨j, ?_⟩
    have hc' : g (((Nat.unpair j).2 : ℝ≥0) * (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) < lower := by
      rw [hj]; exact hc
    rw [if_pos hc']
    convert hT using 1
    rw [← ENNReal.coe_mul, ← ENNReal.coe_mul, hj]
