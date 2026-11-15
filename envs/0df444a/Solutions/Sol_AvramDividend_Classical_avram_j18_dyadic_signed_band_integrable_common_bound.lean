-- Prove2me | solution 1 for AvramDividend.Classical.avram_j18_dyadic_signed_band_integrable_common_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T16:49:42.427205+00:00
-- url     : https://prove2.me/submissions/ccc82cd6-40c8-4157-9344-099c35de8302

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_anoise30_original_smallband_compensator_integrable
import Theorems.Thm_AvramDividend_Classical_avram_anoise38_original_dyadic_integrable_uniform_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ, ∀ s t : ℝ≥0, s ≤ t →
      let B : Set ℝ := Ioc (-1 : ℝ) (-(1 / ((n : ℝ) + 1)))
      let C : ℕ → ℕ → Set ℝ := fun k i =>
        B ∩ Ioc (-1 + (i : ℝ) / (2 : ℝ) ^ k)
          (-1 + ((i : ℝ) + 1) / (2 : ℝ) ^ k)
      let J : ℕ → ℕ → Ω → ℝ≥0∞ := fun k i ω =>
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
          (Ioc s t ×ˢ C k i)
      let M : ℕ → Ω → ℝ := fun k ω =>
        ∑ i ∈ Finset.range (2 ^ k),
          (-1 + (i : ℝ) / (2 : ℝ) ^ k) *
            ((J k i ω).toReal -
              (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (C k i)).toReal)
      ∃ bound : Ω → ℝ, Integrable bound P ∧
        (∀ k, ∀ᵐ ω ∂P, ‖M k ω‖ ≤ bound ω)  := by
  exact avram_anoise38_original_dyadic_integrable_uniform_bound
    X hFinite (avram_anoise30_original_smallband_compensator_integrable X hFinite)
