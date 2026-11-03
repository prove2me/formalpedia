-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_two_sign_cadlag_measurable_candidate_time_enumeration
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:11:08.893581+00:00
-- url     : https://prove2.me/submissions/58be0f05-55f8-412b-abf8-dfb6c138e888

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_countable_rational_first_downcrossing_time_sequence_product_measurable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
attribute [local instance] Classical.propDecidable

/-- Interleaving two measurable rational first-downcrossing clocks covers
every nonzero càdlàg jump, for the path and for its pointwise negation. -/
theorem solution
    (grid : ℕ → ℝ≥0) (hdense : DenseRange grid)
    (pairs : ℕ → ℕ × ℚ) (hpairs : Function.Surjective pairs) :
    ∃ time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0,
      (∀ k, Measurable (time k)) ∧
      ∀ Y : ℝ≥0 → ℝ,
        (∀ u : ℝ≥0, ContinuousWithinAt Y (Ici u) u) →
        (∀ u : ℝ≥0, 0 < u →
          Tendsto Y (𝓝[<] u) (𝓝 (Function.leftLim Y u))) →
        ∀ u : ℝ≥0, 0 < u →
          Y u - Function.leftLim Y u ≠ 0 →
          ∃ k : ℕ, time k Y = u := by
  let m : ℕ → (ℝ≥0 → ℝ) → ℝ≥0 := fun k Y =>
    (⨅ n : ℕ,
      {Z : ℝ≥0 → ℝ |
        grid (pairs k).1 < grid n ∧
        Z (grid n) < ((pairs k).2 : ℝ)}.piecewise
        (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) Y).toNNReal
  let p : ℕ → (ℝ≥0 → ℝ) → ℝ≥0 := fun k Y =>
    m k (fun v : ℝ≥0 => -Y v)
  have hm : Measurable (fun Y : ℝ≥0 → ℝ => fun k : ℕ => m k Y) :=
    avram_wave7_01_countable_rational_first_downcrossing_time_sequence_product_measurable
      grid pairs
  have hNeg : Measurable
      (fun Y : ℝ≥0 → ℝ => fun v : ℝ≥0 => -Y v) := by
    exact measurable_pi_iff.mpr (fun v => (measurable_pi_apply v).neg)
  have hp : Measurable (fun Y : ℝ≥0 → ℝ => fun k : ℕ => p k Y) :=
    hm.comp hNeg
  let time : ℕ → (ℝ≥0 → ℝ) → ℝ≥0 := fun j Y =>
    if Even j then m (j / 2) Y else p (j / 2) Y
  refine ⟨time, ?_, ?_⟩
  · intro j
    by_cases hj : Even j
    · simpa only [time, if_pos hj] using (measurable_pi_iff.mp hm) (j / 2)
    · simpa only [time, if_neg hj] using (measurable_pi_iff.mp hp) (j / 2)
  · intro Y hRight hLeft u hu hjump
    have hCover :=
      avram_wave7_01_all_cadlag_jumps_two_rational_downcrossing_families
        Y hRight hLeft grid hdense pairs hpairs u hu hjump
    rcases hCover with ⟨k, hk⟩ | ⟨k, hk⟩
    · refine ⟨2 * k, ?_⟩
      have heven : Even (2 * k) := ⟨k, by omega⟩
      have hdiv : (2 * k) / 2 = k := by omega
      simpa only [time, if_pos heven, hdiv, m] using hk
    · refine ⟨2 * k + 1, ?_⟩
      have hodd : ¬ Even (2 * k + 1) := by
        rintro ⟨d, hd⟩
        omega
      have hdiv : (2 * k + 1) / 2 = k := by omega
      simpa only [time, if_neg hodd, hdiv, p, m] using hk
