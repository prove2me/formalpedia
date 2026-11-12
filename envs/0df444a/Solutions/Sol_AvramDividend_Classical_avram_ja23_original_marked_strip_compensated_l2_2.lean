-- Prove2me | solution 2 for AvramDividend.Classical.avram_ja23_original_marked_strip_compensated_l2
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:02:36.137731+00:00
-- url     : https://prove2.me/submissions/dff4eff2-da34-472d-b479-378e4f0eeaca
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja25_original_marked_strip_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja24_original_marked_strip_second_moment_of_L2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original physical strip isometry from square integrability and its exact moment identity. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n m : ℕ), n ≤ m → ∀ (t : ℝ≥0),
      let S : Set ℝ :=
        Ioc (-(1 / ((n : ℝ) + 1))) (-(1 / ((m : ℝ) + 1)))
      let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      let C : Ω → ℝ := fun ω =>
        (∫ p in (Ioc 0 t ×ˢ S), p.2 ∂NX ω) -
          (t : ℝ) * (∫ z in S, z ∂X.ν)
      Integrable (fun ω => (C ω) ^ 2) P ∧
      (∫ ω, (C ω) ^ 2 ∂P) =
        (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν) := by
  intro n m hnm t
  have hInt :=
    avram_ja25_original_marked_strip_square_integrable
      X hFinite n m hnm t
  have hEq :=
    avram_ja24_original_marked_strip_second_moment_of_L2
      X hX hFinite n m hnm t hInt
  exact ⟨hInt, hEq⟩
