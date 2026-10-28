-- Prove2me | solution 1 for AvramDividend.Classical.rightInterval_lower_strictExit_eq_schedule
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:07:35.240296+00:00
-- url     : https://prove2.me/submissions/6ecc8c9a-d4dd-4e3c-aff5-1f617cc54043

import Mathlib.Data.ENNReal.Basic
import Mathlib.Data.NNReal.Defs
import Mathlib.Data.Nat.Pairing
import Theorems.Thm_AvramDividend_Classical_rightInterval_lower_before_horizon_grid_iff
import Theorems.Thm_AvramDividend_Classical_firstPassage_iInf_eq_of_strict_horizon_witness_iff
import Theorems.Thm_AvramDividend_Classical_countableSchedule_lower_grid_clock_eq_subtype_inf

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped NNReal ENNReal
open AvramDividend.Classical

/-! The exact right-persistent lower clock uses a single countable schedule. -/
theorem solution
    (g : ℝ≥0 → ℝ) (lower : ℝ)
    (hRight : ∀ s : ℝ≥0, g s < lower →
      ∃ u : ℝ≥0, s < u ∧
        ∀ r : ℝ≥0, s ≤ r → r < u → g r < lower) :
    (⨅ i : {t : ℝ≥0 // g t < lower}, (i.1 : ℝ≥0∞)) =
    (⨅ j : ℕ, if
          g (((Nat.unpair j).2 : ℝ≥0) *
            (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) < lower
        then ((((Nat.unpair j).2 : ℝ≥0) *
          (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹)) : ℝ≥0∞)
        else ⊤) := by
  classical
  trans (⨅ j : {p : ℕ × ℕ // 0 < p.1 ∧
      g ((p.2 : ℝ≥0) * (p.1 : ℝ≥0)⁻¹) < lower},
      (((j.1.2 : ℝ≥0) * (j.1.1 : ℝ≥0)⁻¹) : ℝ≥0∞))
  · apply firstPassage_iInf_eq_of_strict_horizon_witness_iff
    intro T
    induction T using ENNReal.recTopCoe with
    | top =>
      constructor
      · rintro ⟨⟨t, ht⟩, -⟩
        obtain ⟨n, hn, k, -, hX⟩ :=
          (rightInterval_lower_before_horizon_grid_iff
            g lower hRight (t + 1)).1 ⟨t, lt_add_one t, ht⟩
        exact ⟨⟨(n, k), hn, hX⟩, ENNReal.coe_lt_top⟩
      · rintro ⟨⟨p, hp, hX⟩, -⟩
        exact ⟨⟨_, hX⟩, ENNReal.coe_lt_top⟩
    | coe T =>
      have h := rightInterval_lower_before_horizon_grid_iff
        g lower hRight T
      constructor
      · rintro ⟨⟨t, ht⟩, htT⟩
        obtain ⟨n, hn, k, hk, hX⟩ :=
          h.1 ⟨t, ENNReal.coe_lt_coe.1 htT, ht⟩
        exact ⟨⟨(n, k), hn, hX⟩, ENNReal.coe_lt_coe.2 hk⟩
      · rintro ⟨⟨p, hp, hX⟩, hpT⟩
        exact ⟨⟨_, hX⟩, hpT⟩
  · exact (countableSchedule_lower_grid_clock_eq_subtype_inf g lower).symm
