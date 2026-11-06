-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn9_original_stopped_contact_prefix_card_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T22:01:23.832406+00:00
-- url     : https://prove2.me/submissions/0ac688ba-62f9-4867-a4d3-16a1804ea0fe

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The exact random strict-prefix cardinal from the original stopped
contact-cell partition is a measurable, bounded Nat-valued selector. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ≥0) (m : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → Ω → ℝ≥0 := fun j ω =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) (τ ω)
    let k : Ω → ℕ := fun ω =>
      ((Finset.range (m + 1)).filter
        (fun i => u (i + 1) ω < τ ω)).card
    Measurable k ∧ ∀ ω, k ω ≤ m + 1 := by
  dsimp
  have hτ : Measurable (fun ω : Ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) := by
    exact ENNReal.measurable_toNNReal.comp
      ((ruinTime_measurable X x D hD.1.1).min measurable_const)
  constructor
  · classical
    simp_rw [Finset.card_filter]
    apply Finset.measurable_sum
    intro j hj
    have hs : MeasurableSet {ω : Ω |
        (min (((min (j + 1) (m + 1) : ℕ) : ℝ≥0) *
          (T / (m + 1)))
          (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal) <
          (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal} :=
      measurableSet_lt (measurable_const.min hτ) hτ
    exact Measurable.ite hs measurable_const measurable_const
  · intro ω
    have hsub :
        ((Finset.range (m + 1)).filter
          (fun i =>
            min (((min (i + 1) (m + 1) : ℕ) : ℝ≥0) *
                (T / (m + 1)))
              (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal <
              (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal))
          ⊆ Finset.range (m + 1) := Finset.filter_subset _ _
    exact (Finset.card_le_card hsub).trans (by simp)
