-- Prove2me | solution 4 for AvramDividend.Classical.avram_ja23_original_marked_strip_compensated_l2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T10:19:53.524525+00:00
-- url     : https://prove2.me/submissions/653ba39f-5222-441b-bc92-b7917d238abd

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ja26_original_marked_strip_compensated_square_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ja24_original_marked_strip_second_moment_of_L2
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

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
  change Integrable (fun ω => (C ω) ^ 2) P ∧
    (∫ ω, (C ω) ^ 2 ∂P) =
      (t : ℝ) * (∫ z in S, z ^ 2 ∂X.ν)
  have hSq : Integrable (fun ω => (C ω) ^ 2) P := by
    simpa only [C, S, NX] using
      (avram_ja26_original_marked_strip_compensated_square_integrable
        X hX hFinite n m hnm t)
  refine ⟨hSq, ?_⟩
  simpa only [C, S, NX] using
    (avram_ja24_original_marked_strip_second_moment_of_L2
      X hX hFinite n m hnm t hSq)
