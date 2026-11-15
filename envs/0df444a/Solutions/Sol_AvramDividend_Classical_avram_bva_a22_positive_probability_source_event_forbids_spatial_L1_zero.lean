-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_positive_probability_source_event_forbids_spatial_L1_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T07:51:50.961483+00:00
-- url     : https://prove2.me/submissions/0d54a340-9e59-4af3-8172-aac75a8d5ec5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_persistent_integrable_positive_witness_forbids_spatial_L1_zero
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
/- A positive probability event with an eventual error floor yields a fixed
   integrable positive witness, contradicting vanishing positive L1 error. -/

theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < P A)
    (ε : ℝ) (hε : 0 < ε) (E : ℕ → Ω → ℝ)
    (hEI : ∀ m, Integrable (fun ω => max (E m ω) 0) P)
    (hEvent : ∀ᶠ m : ℕ in atTop,
      ∀ᵐ ω ∂P, ω ∈ A → ε ≤ E m ω) :
    ¬ Tendsto (fun m => ∫ ω, max (E m ω) 0 ∂P)
      atTop (𝓝 (0 : ℝ)) := by
  classical
  let g : Ω → ℝ := A.indicator (fun _ => ε)
  have hGI : Integrable g P :=
    (integrable_const _).indicator hA
  have hgPos : 0 < ∫ ω, g ω ∂P := by
    change 0 < ∫ ω, A.indicator (fun _ : Ω => ε) ω ∂P
    rw [integral_indicator_const ε hA]
    exact mul_pos
      ((ENNReal.toReal_pos_iff).2 ⟨hApos, measure_lt_top P A⟩) hε
  have hDom : ∀ᶠ m : ℕ in atTop,
      ∀ᵐ ω ∂P, g ω ≤ max (E m ω) 0 := by
    filter_upwards [hEvent] with m hm
    filter_upwards [hm] with ω hω
    by_cases ha : ω ∈ A
    · simpa only [g, Set.indicator_of_mem ha] using
        (le_trans (hω ha) (le_max_left (E m ω) 0))
    · simp [g, Set.indicator_of_notMem ha, le_max_right]
  exact avram_bva_a22_persistent_integrable_positive_witness_forbids_spatial_L1_zero
    P E g hEI hGI hgPos hDom
