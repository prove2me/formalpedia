-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_finite_jumpfree_compensated_residual_constant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T09:50:29.985863+00:00
-- url     : https://prove2.me/submissions/1b638da3-73a9-4664-b004-72ca3c630c37

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_finset_step_no_new_mark_equal
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ) (drift : ℝ) (S : Finset ℝ≥0)
    (s t : ℝ≥0) (hst : s ≤ t)
    (hCover : ∀ u ∈ Set.Ioc s t,
       f u - Function.leftLim f u ≠ 0 → u ∈ S)
    (hNo : ∀ u ∈ S, ¬ (s < u ∧ u ≤ t))
    (hFlat : (∀ u ∈ Set.Ioc s t,
        f u - Function.leftLim f u = 0) →
        (t : ℝ) * drift - f t = (s : ℝ) * drift - f s) :
    (t : ℝ) * drift - f t -
      Finset.sum S (fun u => if u ≤ t then Function.leftLim f u - f u else 0) =
    (s : ℝ) * drift - f s -
      Finset.sum S (fun u => if u ≤ s then Function.leftLim f u - f u else 0) := by
  have hNoJump : ∀ u ∈ Set.Ioc s t,
      f u - Function.leftLim f u = 0 := by
    intro u hu
    by_contra hneq
    have hmem : u ∈ S := hCover u hu hneq
    exact hNo u hmem ⟨hu.1, hu.2⟩
  have hf := hFlat hNoJump
  have hs := avram_bva_finset_step_no_new_mark_equal
    S (fun u => Function.leftLim f u - f u) s t hst hNo
  linarith
