-- Prove2me | solution 1 for AvramDividend.Classical.avram_b196_reciprocal_negative_mark_bands_exhaust_all_negative_marks
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:15:08.636021+00:00
-- url     : https://prove2.me/submissions/be083484-218b-4c0a-9f1d-b74e96263e9d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

/-- The increasing original reciprocal negative mark bands exhaust exactly the strictly negative real marks. -/
theorem solution :
    (⋃ n : ℕ, Iic (-(1 / ((n : ℝ) + 1)))) =
      Iio (0 : ℝ) := by
  ext z
  constructor
  · intro hz
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hz
    have hp : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    change z ≤ -(1 / ((n : ℝ) + 1)) at hn
    change z < 0
    linarith
  · intro hz
    have hneg : z < (0 : ℝ) := hz
    have hlim : Tendsto
        (fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1))
        atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have he : ∀ᶠ n : ℕ in atTop,
        (1 : ℝ) / ((n : ℝ) + 1) < -z :=
      hlim.eventually (isOpen_Iio.mem_nhds (neg_pos.mpr hneg))
    obtain ⟨n, hn⟩ := he.exists
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    change z ≤ -(1 / ((n : ℝ) + 1))
    linarith
