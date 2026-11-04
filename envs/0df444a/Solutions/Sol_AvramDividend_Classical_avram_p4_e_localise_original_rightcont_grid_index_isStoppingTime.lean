-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_rightcont_grid_index_isStoppingTime
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:34:56.744203+00:00
-- url     : https://prove2.me/submissions/31cf10d1-b103-4a64-99be-8c3ebfe6293d

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Adapt source right-continuous sampled events into a bounded discrete stopping time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℝ≥0) (he : Monotone e)
    (𝓖 : Filtration ℕ mΩ)
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (e i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (he hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (e i) } : Filtration ℕ mΩ))
    (K : Ω → ℕ)
    (hEvents : ∀ i, MeasurableSet[𝓕.rightCont (e i)] {ω : Ω | K ω ≤ i})
    (N : ℕ) (hBound : ∀ ω, K ω ≤ N) :
    IsStoppingTime 𝓖 (fun ω => (K ω : WithTop ℕ)) ∧
      ∀ ω, (K ω : WithTop ℕ) ≤ (N : WithTop ℕ) := by
  constructor
  · intro i
    have hFil : 𝓖 i = 𝓕.rightCont (e i) := by
      rw [h𝓖]
    have hevent : MeasurableSet[𝓖 i] {ω : Ω | K ω ≤ i} := by
      rw [hFil]
      exact hEvents i
    simpa using hevent
  · intro ω
    exact_mod_cast hBound ω
