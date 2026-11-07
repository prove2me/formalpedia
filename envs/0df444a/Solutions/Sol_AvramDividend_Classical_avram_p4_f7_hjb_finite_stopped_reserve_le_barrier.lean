-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_f7_hjb_finite_stopped_reserve_le_barrier
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T10:45:18.915253+00:00
-- url     : https://prove2.me/submissions/87b77be9-d5c0-487d-b11b-532f65cf8070

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_path_value_le_of_strict_prefix_le

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Before any clipped original strict upper exit, no observation can exceed
the upper level. Spectral negativity preserves the bound at the clipped stop. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (b : ℝ) (n : ℕ) (hb : 1 ≤ b) (ω : Ω) :
    X.X
      (ENNReal.toNNReal
        (min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞)))) ω ≤
      b - 1 := by
  let U : ℝ≥0∞ := twoSidedExitUpTimeCorrected X (b - 1) ω
  let D : ℝ≥0∞ := twoSidedExitDownTimeCorrected X (-1) ω
  let e : ℝ≥0∞ := min U (min D (n : ℝ≥0∞))
  let u : ℝ≥0 := e.toNNReal
  have he_le_n : e ≤ (n : ℝ≥0∞) := by
    exact le_trans (min_le_right U _) (min_le_right D _)
  have he_fin : e ≠ ⊤ := ne_top_of_le_ne_top (by simp) he_le_n
  have hu_coe : (u : ℝ≥0∞) = e := ENNReal.coe_toNNReal he_fin
  have hu_le_U : (u : ℝ≥0∞) ≤ U := by
    rw [hu_coe]
    exact min_le_left _ _
  change X.X u ω ≤ b - 1
  apply path_value_le_of_strict_prefix_le X (b - 1) (by linarith) ω u
  intro t ht
  by_contra hfail
  have hbad : b - 1 < X.X t ω := lt_of_not_ge hfail
  have hfirst : U ≤ (t : ℝ≥0∞) := by
    dsimp [U, twoSidedExitUpTimeCorrected]
    exact iInf_le_of_le t (iInf_le_of_le hbad le_rfl)
  have htcoe : (t : ℝ≥0∞) < (u : ℝ≥0∞) :=
    ENNReal.coe_lt_coe.mpr ht
  exact (not_lt_of_ge (le_trans hu_le_U hfirst)) htcoe
