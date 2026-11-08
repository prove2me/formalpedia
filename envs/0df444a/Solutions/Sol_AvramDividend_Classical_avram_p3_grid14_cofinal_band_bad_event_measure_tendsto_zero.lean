-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid14_cofinal_band_bad_event_measure_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T16:32:51.165379+00:00
-- url     : https://prove2.me/submissions/12b2766a-cfad-496f-9593-4e58c48c9bb3

import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    [IsFiniteMeasure P] (C : ℝ≥0∞) (a b : ℕ → ℝ)
    (hExh : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ k ≥ N, y ∈ Icc (a k) (b k))
    (n : ℕ) (z : Ω → ℕ → ℝ)
    (hz : ∀ i, Measurable (fun ω => z ω i)) :
    Tendsto (fun k : ℕ =>
      P ({ω : Ω | ∀ i < n + 1,
        (0 < z ω i ∧ ENNReal.ofReal (z ω i) < C) →
          z ω i ∈ Icc (a k) (b k)}ᶜ))
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  classical
  let G : ℕ → Set Ω := fun k =>
    {ω | ∀ i < n + 1,
      (0 < z ω i ∧ ENNReal.ofReal (z ω i) < C) →
        z ω i ∈ Icc (a k) (b k)}
  have hG (k : ℕ) : MeasurableSet (G k) := by
    dsimp [G]
    measurability
  have hEventually (ω : Ω) :
      ∃ N : ℕ, ∀ k ≥ N, ω ∈ G k := by
    obtain ⟨N, hN⟩ :=
      avram_p3_grid4_turn13_original_finite_row_interior_mask_eventually
        C a b hExh n (z ω)
    exact ⟨N, fun k hk i hi hzi => hN k hk i hi hzi⟩
  let B : ℕ → Set Ω := fun k =>
    {ω | ∃ j : ℕ, k ≤ j ∧ ω ∉ G j}
  have hBm (k : ℕ) : MeasurableSet (B k) := by
    dsimp [B]
    measurability
  have hanti : Antitone B := by
    intro k l hkl ω hω
    obtain ⟨j, hj, hbad⟩ := hω
    exact ⟨j, le_trans hkl hj, hbad⟩
  have hEmpty : (⋂ k : ℕ, B k) = ∅ := by
    ext ω
    constructor
    · intro hω
      obtain ⟨N, hN⟩ := hEventually ω
      obtain ⟨j, hj, hbad⟩ := (Set.mem_iInter.mp hω) N
      exact (hbad (hN j hj)).elim
    · intro hω
      simp at hω
  have hlim := tendsto_measure_iInter_atTop (μ := P)
    (s := B)
    (fun k => (hBm k).nullMeasurableSet)
    hanti ⟨0, measure_ne_top _ _⟩
  rw [hEmpty, measure_empty] at hlim
  change Tendsto (fun k : ℕ => P ((G k)ᶜ)) atTop (𝓝 (0 : ℝ≥0∞))
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hlim
  · intro k
    exact bot_le
  · intro k
    apply measure_mono
    intro ω hω
    exact ⟨k, le_rfl, hω⟩
