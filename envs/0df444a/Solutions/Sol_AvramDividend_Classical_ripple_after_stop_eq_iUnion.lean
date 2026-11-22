-- Prove2me | solution 1 for AvramDividend.Classical.ripple_after_stop_eq_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T10:55:18.703886+00:00
-- url     : https://prove2.me/submissions/e2d9d0df-0628-4c4e-81d5-4b37c2cafc2f

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.SetSemiring

open MeasureTheory Set
/-- Rational predictable rectangles describe the strict post-stopping region.
Proof adapted from zinan-huang/Ripple (Apache-2.0), commit
e216e28ce3ffb43877e11f71be260e40a37a35df. -/
theorem solution
    {Ω : Type*} (τ : Ω → WithTop NNReal) :
    {z : NNReal × Ω | τ z.2 < (z.1 : WithTop NNReal)} =
      ⋃ q : ℚ, Ioi (Real.toNNReal (q : ℝ)) ×ˢ
        {ω | τ ω ≤ (Real.toNNReal (q : ℝ) : WithTop NNReal)} := by
  ext z
  simp only [mem_setOf_eq, mem_iUnion, mem_prod, mem_Ioi]
  constructor
  · intro hz
    cases he : τ z.2 with
    | top => simp [he] at hz
    | coe a =>
      have hat : a < z.1 := by
        simpa only [he, WithTop.coe_lt_coe] using hz
      obtain ⟨q, haq, hqt⟩ := exists_rat_btwn
        (show (a : ℝ) < (z.1 : ℝ) from by exact_mod_cast hat)
      have hqnonneg : 0 ≤ (q : ℝ) := a.coe_nonneg.trans haq.le
      have hcut : (Real.toNNReal (q : ℝ) : ℝ) = (q : ℝ) :=
        Real.coe_toNNReal _ hqnonneg
      have hcutlt : Real.toNNReal (q : ℝ) < z.1 := by
        exact_mod_cast (show (Real.toNNReal (q : ℝ) : ℝ) < (z.1 : ℝ) by
          rw [hcut]
          exact hqt)
      have hcutge : a ≤ Real.toNNReal (q : ℝ) := by
        exact_mod_cast (show (a : ℝ) ≤ (Real.toNNReal (q : ℝ) : ℝ) by
          rw [hcut]
          exact haq.le)
      exact ⟨q, hcutlt, by simpa only [he, WithTop.coe_le_coe] using hcutge⟩
  · rintro ⟨q, hqt, hτq⟩
    exact lt_of_le_of_lt hτq (WithTop.coe_lt_coe.mpr hqt)
