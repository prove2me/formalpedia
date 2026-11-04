-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_sigma_finite_of_negative_tail_cover
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:58:05.124702+00:00
-- url     : https://prove2.me/submissions/33b63f1d-cf0d-43bc-afae-ac32e4ba2df1

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_countable_finite_negative_support_cover
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical

/-- The explicit measurable finite-mass cover gives sigma-finiteness for
every real mark measure with strict negative support and finite negative tails. -/
theorem solution
    (μ : Measure ℝ)
    (hzero : μ (Ici (0 : ℝ)) = 0)
    (hfin : ∀ ε : ℝ, 0 < ε → μ (Iic (-ε)) < ⊤) :
    SigmaFinite μ := by
  obtain ⟨C, _, hFinite, hCover⟩ :=
    avram_p2_c_borel_countable_finite_negative_support_cover μ hzero hfin
  refine Measure.sigmaFinite_of_countable (S := Set.range C)
    (Set.countable_range C) ?_ ?_
  · intro s hs
    obtain ⟨n, rfl⟩ := hs
    exact hFinite n
  · simpa only [Set.sUnion_range] using hCover
