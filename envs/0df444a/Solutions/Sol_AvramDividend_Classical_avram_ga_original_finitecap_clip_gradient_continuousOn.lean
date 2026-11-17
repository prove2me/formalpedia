-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_original_finitecap_clip_gradient_continuousOn
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:02:10.549256+00:00
-- url     : https://prove2.me/submissions/09f13c9a-fca1-4621-8055-c5bae89fec37

import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_finitecap_rational_clip_strict_interior
import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
theorem solution
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ContinuousOn (deriv w) (Icc a b) := by
  let a : ℝ := δ / 2
  let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
  let U : Set ℝ := {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}
  have hb : 0 < b ∧ ENNReal.ofReal b < C := by
    simpa only [b] using
      (avram_gbB41_original_finitecap_rational_clip_strict_interior
        C hC hFiniteCap j)
  have ha : 0 < a := by dsimp [a]; positivity
  have hOpen : IsOpen U := by
    change IsOpen ({y : ℝ | 0 < y} ∩
      {y : ℝ | ENNReal.ofReal y < C})
    apply IsOpen.inter
    · exact isOpen_Ioi
    · exact isOpen_Iio.preimage ENNReal.continuous_ofReal
  have hSub : Icc a b ⊆ U := by
    intro y hy
    change 0 < y ∧ ENNReal.ofReal y < C
    refine ⟨lt_of_lt_of_le ha hy.1, ?_⟩
    exact (ENNReal.ofReal_le_ofReal hy.2).trans_lt hb.2
  have hCont : ContinuousOn (deriv w) U :=
    hw.continuousOn_deriv_of_isOpen hOpen (by norm_num)
  simpa only [a, b] using (hCont.mono hSub)
