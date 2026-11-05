-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_right_continuous_grid_detection
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:27:17.545288+00:00
-- url     : https://prove2.me/submissions/707cb796-46a8-4577-961c-8623009cb1bc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (r : ℕ → ℝ≥0) (lower upper : ℝ)
    (hgrid : ∀ (s t : ℝ≥0), s < t →
      ∀ U : Set ℝ≥0, U ∈ 𝓝[Set.Ici s] s →
        ∃ k, r k < t ∧ r k ∈ U) :
    ∀ ω (s t : ℝ≥0), s < t →
      (x + X.X s ω - rightLimit D s ω < lower ∨
        upper < x + X.X s ω - rightLimit D s ω) →
      ∃ k, r k < t ∧
        (x + X.X (r k) ω - rightLimit D (r k) ω < lower ∨
          upper < x + X.X (r k) ω - rightLimit D (r k) ω) := by
  intro ω s t hst hex
  have hcont : ContinuousWithinAt
      (fun u : ℝ≥0 => x + X.X u ω - rightLimit D u ω)
      (Set.Ici s) s :=
    (postPaymentReserve_cadlag_adapted X x D hD).1 ω s
  have hopen : IsOpen (Set.Iio lower ∪ Set.Ioi upper) :=
    isOpen_Iio.union isOpen_Ioi
  have hmem : x + X.X s ω - rightLimit D s ω ∈
      Set.Iio lower ∪ Set.Ioi upper := by
    simpa [Set.mem_union, Set.mem_Iio, Set.mem_Ioi] using hex
  have hlocal :
      {u : ℝ≥0 | x + X.X u ω - rightLimit D u ω < lower ∨
          upper < x + X.X u ω - rightLimit D u ω} ∈
      𝓝[Set.Ici s] s := by
    have he : ∀ᶠ u : ℝ≥0 in 𝓝[Set.Ici s] s,
        x + X.X u ω - rightLimit D u ω ∈
          Set.Iio lower ∪ Set.Ioi upper :=
      hcont.eventually (hopen.mem_nhds hmem)
    apply Filter.mem_of_superset he
    intro u hu
    exact hu
  obtain ⟨k, hk, hku⟩ := hgrid s t hst _ hlocal
  exact ⟨k, hk, hku⟩