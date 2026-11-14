-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_capHJB48_original_BV_candidate_bounded_by_closed_cap_value
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T22:49:36.863532+00:00
-- url     : https://prove2.me/submissions/df0094f5-665c-4ea5-8829-7c8252b67491

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.SetSemiring
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/- Current-checker revalidation of exact full finite-cap original BV C1 monotone-candidate bound. -/
theorem solution
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hwCont : ContinuousOn w (Ici (0 : ℝ)))
    (hw0 : 0 ≤ w 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    0 ≤ w C.toReal ∧
    ∀ y ∈ Icc (0 : ℝ) C.toReal, |w y| ≤ w C.toReal := by
  have hpos : 0 ≤ C.toReal :=
    ENNReal.toReal_nonneg
  have hmono : MonotoneOn w (Icc (0 : ℝ) C.toReal) :=
    avram_bva_a22_original_C1_candidate_monotone_closed_reserve_band
      C hC w hwCont hwSmooth hwGrad C.toReal (Or.inr le_rfl)
  have hwCap : 0 ≤ w C.toReal :=
    hw0.trans (hmono ⟨le_refl _, hpos⟩ ⟨hpos, le_refl _⟩ hpos)
  refine ⟨hwCap, ?_⟩
  intro y hy
  have hy0 : 0 ≤ w y :=
    hw0.trans (hmono ⟨le_refl _, hpos⟩ hy hy.1)
  have hyC : w y ≤ w C.toReal :=
    hmono hy ⟨hpos, le_refl _⟩ hy.2
  simpa only [abs_of_nonneg hy0] using hyC
