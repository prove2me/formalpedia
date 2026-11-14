-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_marked_negative_kernel_cofinal_mask_pointwise_eventually_exact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:18.905342+00:00
-- url     : https://prove2.me/submissions/d6181a19-3ca8-4179-bdad-008494967226

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n)) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    ∀ (S : ℝ≥0) (ω : Ω) (t : ℝ≥0) (z : ℝ),
      (t : ℝ≥0∞) ≤ min (ruinTime X x D ω) (S : ℝ≥0∞) →
      0 < Y t ω → ENNReal.ofReal (Y t ω) < C →
      z < 0 →
      ∀ᶠ n : ℕ in atTop,
        (if (((t : ℝ≥0∞) ≤
          min (ruinTime X x D ω) (S : ℝ≥0∞) ∧
          Y t ω ∈ Icc (a n) (b n)) ∧ z < 0) then
          Real.exp (-(q * (t : ℝ))) *
            (w (Y t ω + z) - w (Y t ω))
        else 0) =
          Real.exp (-(q * (t : ℝ))) *
            (w (Y t ω + z) - w (Y t ω)) := by
  intro Y S ω t z ht hpos hcap hz
  obtain ⟨N, hN⟩ := hcover (Y t ω) hpos hcap
  filter_upwards [eventually_ge_atTop N] with n hn
  have hmask : ((t : ℝ≥0∞) ≤
      min (ruinTime X x D ω) (S : ℝ≥0∞) ∧
      Y t ω ∈ Icc (a n) (b n)) ∧ z < 0 :=
    ⟨⟨ht, hN n hn⟩, hz⟩
  rw [if_pos hmask]
