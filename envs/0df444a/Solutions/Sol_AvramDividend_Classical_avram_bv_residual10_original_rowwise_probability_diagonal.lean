-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_residual10_original_rowwise_probability_diagonal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:30:51.929475+00:00
-- url     : https://prove2.me/submissions/440a1a46-1f20-40fb-bd62-7e9848d1d5fe

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- In the original refining grid, a deterministic bound can be selected
independently for every physical row. The discarded-event probability
vanishes without assuming any L1 generator envelope. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsFiniteMeasure P]
    (a : ℕ → Ω → ℕ → ℝ)
    (ha : ∀ n i, Measurable (fun ω => a n ω i))
    (ε : ℕ → ℝ≥0∞) (hεpos : ∀ n, 0 < ε n)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ≥0∞))) :
    ∃ K : ℕ → ℕ,
      (∀ n, P ({ω : Ω | ∀ i ∈ Finset.range (n + 1),
        abs (a n ω i) ≤ (K n : ℝ)}ᶜ) < ε n) ∧
      Tendsto
        (fun n => P ({ω : Ω | ∀ i ∈ Finset.range (n + 1),
          abs (a n ω i) ≤ (K n : ℝ)}ᶜ))
        atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let A : ℕ → ℕ → Set Ω := fun n k =>
    {ω | ∀ i ∈ Finset.range (n + 1), abs (a n ω i) ≤ (k : ℝ)}
  have hchoose (n : ℕ) : ∃ k : ℕ, P ((A n k)ᶜ) < ε n := by
    have hlim :=
      avram_bv_residual10_finite_coordinate_event_compl_measure_tendsto
        (P := P) n (a n) (ha n)
    have hevent : ∀ᶠ k : ℕ in atTop, P ((A n k)ᶜ) < ε n :=
      hlim.eventually (eventually_lt_nhds (hεpos n))
    exact hevent.exists
  let K : ℕ → ℕ := fun n => Classical.choose (hchoose n)
  have hbound (n : ℕ) : P ((A n (K n))ᶜ) ≤ ε n :=
    le_of_lt (Classical.choose_spec (hchoose n))
  refine ⟨K, ?_, ?_⟩
  · intro n
    exact Classical.choose_spec (hchoose n)
  · apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds :
        Tendsto (fun _ : ℕ => (0 : ℝ≥0∞)) atTop (𝓝 (0 : ℝ≥0∞)))
      hεlim
    · exact Filter.Eventually.of_forall (fun _ => bot_le)
    · exact Filter.Eventually.of_forall hbound
