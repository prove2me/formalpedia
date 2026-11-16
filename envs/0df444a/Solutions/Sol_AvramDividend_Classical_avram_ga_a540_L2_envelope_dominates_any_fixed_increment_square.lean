-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a540_L2_envelope_dominates_any_fixed_increment_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:52:44.772364+00:00
-- url     : https://prove2.me/submissions/75ef773c-1c12-4576-916b-e4dae042e912

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (M : ℝ≥0 → Ω → ℝ) (T s t : ℝ≥0)
    (hs : s ≤ T) (ht : t ≤ T)
    (hMeas : ∀ r : ℝ≥0, r ≤ T →
      AEStronglyMeasurable (M r) P)
    (S : Ω → ℝ) (hS : Integrable S P)
    (hDom : ∀ᵐ ω ∂P, 0 ≤ S ω ∧
      ∀ r : ℝ≥0, r ≤ T → (M r ω)^2 ≤ S ω) :
    Integrable (fun ω => (M t ω - M s ω)^2) P := by
  have hMeas' : AEStronglyMeasurable
      (fun ω => (M t ω - M s ω)^2) P :=
    ((hMeas t ht).sub (hMeas s hs)).pow 2
  have hb : Integrable (fun ω => 4 * S ω) P := hS.const_mul 4
  apply hb.mono_nonneg hMeas'
    (Filter.Eventually.of_forall fun ω => sq_nonneg _)
  filter_upwards [hDom] with ω hω
  have ht' := hω.2 t ht
  have hs' := hω.2 s hs
  have hsq := sq_nonneg (M t ω + M s ω)
  have hsq2 := sq_nonneg (M t ω - M s ω)
  nlinarith
