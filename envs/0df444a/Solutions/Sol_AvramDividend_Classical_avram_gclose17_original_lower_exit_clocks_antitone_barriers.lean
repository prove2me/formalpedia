-- Prove2me | solution 1 for AvramDividend.Classical.avram_gclose17_original_lower_exit_clocks_antitone_barriers
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T23:17:15.603893+00:00
-- url     : https://prove2.me/submissions/2a2c2e31-bb2f-4c04-875d-9d97c65127d2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Lowering the observed reserve threshold postpones its first sampled
violation, and clipping under the same clock preserves this order. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (σ : Ω → WithTop ℝ≥0) (r : ℕ → ℝ≥0)
    (δ : ℕ → ℝ) (hδ : Antitone δ) :
    ∀ ω, Monotone (fun n : ℕ =>
      min (σ ω) (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ n
        then (r k : WithTop ℝ≥0) else ⊤)) := by
  intro ω i j hij
  have hE :
      (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ i
        then (r k : WithTop ℝ≥0) else ⊤) ≤
      (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < δ j
        then (r k : WithTop ℝ≥0) else ⊤) := by
    apply le_iInf
    intro k
    by_cases hj : x + X.X (r k) ω - rightLimit D (r k) ω < δ j
    · have hi : x + X.X (r k) ω - rightLimit D (r k) ω < δ i :=
        lt_of_lt_of_le hj (hδ hij)
      simpa [hi, hj] using
        (iInf_le (fun k : ℕ =>
          if x + X.X (r k) ω - rightLimit D (r k) ω < δ i
          then (r k : WithTop ℝ≥0) else ⊤) k)
    · simp [hj]
  exact min_le_min_left (σ ω) hE
