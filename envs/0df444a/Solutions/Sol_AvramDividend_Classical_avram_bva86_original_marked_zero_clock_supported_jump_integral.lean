-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva86_original_marked_zero_clock_supported_jump_integral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:38:36.176382+00:00
-- url     : https://prove2.me/submissions/6f3e28ba-7709-4af9-8489-6ba81a5d81a7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bva85_original_marked_jump_measure_zero_initial_fibre
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hMeas : Measurable (fun u : ℝ≥0 =>
      (u, X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    (H : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hSupport : ∀ p : ℝ≥0 × ℝ, H ((p.1, ω), p.2) ≠ 0 → p.1 = 0) :
    (∫ p, H ((p.1, ω), p.2)
      ∂((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) = 0 := by
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  have hNull : NX (({0} : Set ℝ≥0) ×ˢ (Set.univ : Set ℝ)) = 0 :=
    avram_bva85_original_marked_jump_measure_zero_initial_fibre X ω hMeas
  have hSet :
      {p : ℝ≥0 × ℝ | ¬ p.1 ≠ 0} =
        (({0} : Set ℝ≥0) ×ˢ (Set.univ : Set ℝ)) := by
    ext p
    simp
  have hAE : ∀ᵐ p ∂NX, p.1 ≠ 0 := by
    apply (ae_iff).2
    simpa only [hSet] using hNull
  apply integral_eq_zero_of_ae
  filter_upwards [hAE] with p hp
  by_cases hz : H ((p.1, ω), p.2) = 0
  · exact hz
  · exact False.elim (hp (hSupport p hz))
