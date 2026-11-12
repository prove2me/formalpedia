-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja29_original_finite_borel_mark_simple_isometry
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:07:08.471143+00:00
-- url     : https://prove2.me/submissions/c7684079-85bb-4548-9c71-de91e59c34a3

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_annulus15_finite_weight_L2_of_physical_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

/-- Apply the proved finite weighted quadratic identity to original marked counts. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0)
    (F : Finset ι) (B : ι → Set ℝ) (a : ι → ℝ)
    (hB : ∀ i ∈ F, MeasurableSet (B i))
    (hDisj : ∀ i ∈ F, ∀ j ∈ F, i ≠ j → Disjoint (B i) (B j)) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let r : ι → ℝ := fun i =>
      ((T : ℝ≥0∞) * X.ν (B i)).toReal
    let Y : ι → Ω → ℝ := fun i ω =>
      (NX ω (Ioc 0 T ×ˢ B i)).toReal - r i
    (∀ i ∈ F, Integrable (fun ω => (Y i ω) ^ 2) P ∧
      (∫ ω, (Y i ω) ^ 2 ∂P) = r i) →
    (∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      Integrable (fun ω => Y i ω * Y j ω) P ∧
      (∫ ω, Y i ω * Y j ω ∂P) = 0) →
    Integrable (fun ω => (∑ i ∈ F, a i * Y i ω) ^ 2) P ∧
      (∫ ω, (∑ i ∈ F, a i * Y i ω) ^ 2 ∂P) =
        ∑ i ∈ F, (a i) ^ 2 * r i := by
  dsimp only
  intro hDiag hOff
  exact avram_mix_annulus15_finite_weight_L2_of_physical_moments
    F _ a _ hDiag hOff
