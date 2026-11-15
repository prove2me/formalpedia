-- Prove2me | solution 1 for AvramDividend.Classical.avram_b123_original_actual_jumpfree_implies_every_negative_count_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T08:01:29.017078+00:00
-- url     : https://prove2.me/submissions/0839d8ea-bf15-402e-8aa8-b8c2ee24b246

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_interval_negative_band_count_ncard
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (hNoJump : ∀ u : ℝ≥0, s < u → u ≤ t →
      X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u = 0)
    (n : ℕ) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iic (-(1 / ((n : ℝ) + 1)))) = 0 := by
  rw [avram_p2_e_compensator_original_interval_negative_band_count_ncard
    X ω s t hst n]
  have hEmpty :
      {u : ℝ≥0 | s < u ∧ u ≤ t ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))} = ∅ := by
    ext u
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    rintro ⟨hsu, hut, hmark⟩
    have hz := hNoJump u hsu hut
    rw [hz] at hmark
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  rw [hEmpty]
  simp
