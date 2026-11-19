-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_reward63_compact_clipped_firstorder_discounted_mark_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T19:12:08.696221+00:00
-- url     : https://prove2.me/submissions/ab3c04a1-2b1d-4674-b950-2cf1cf8e9530

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_compact_derivative_bounded
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward58_nonnegative_discount_bounded_smallmark_product
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (q : ℝ) (hq : 0 ≤ q)
    (w : ℝ → ℝ) (Cband u v δ η : ℝ)
    (hwCb : ContDiffOn ℝ 2 w (Ioo 0 Cband))
    (hleft : 0 < u + δ) (hband : u + δ < v)
    (hv : v < Cband) (hη : 0 < η) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ (t : ℝ≥0) (ω : Ω) (z : ℝ),
        z ∈ Ioo (-1 : ℝ) (-η) →
        |Real.exp (-(q * (t : ℝ))) *
          (if Y t ω ∈ Icc (u + δ) v then
            deriv w (Y t ω) * z else 0)| ≤ M := by
  obtain ⟨M, hMd⟩ :=
    avram_p4_c_generator_compact_derivative_bounded
      w Cband (u + δ) v hwCb hleft hv
  have hM : 0 ≤ M :=
    (abs_nonneg _).trans (hMd _ (left_mem_Icc.mpr (le_of_lt hband)))
  refine ⟨M, hM, ?_⟩
  intro t ω z hz
  by_cases hy : Y t ω ∈ Icc (u + δ) v
  · have hz0 : z < 0 := lt_trans hz.2 (neg_neg_of_pos hη)
    have hsmall : |z| ≤ 1 := by
      rw [abs_of_neg hz0]; linarith [hz.1]
    simpa [hy] using
      (avram_pj_reward58_nonnegative_discount_bounded_smallmark_product
        q hq t z (deriv w (Y t ω)) M hsmall hM (hMd _ hy))
  · simp [hy, hM]
