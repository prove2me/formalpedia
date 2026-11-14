-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_marked_negative_jump_kernel_eventually_unmasked_on_any_fixed_compact
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:17.522597+00:00
-- url     : https://prove2.me/submissions/7b8a422f-0201-4445-ae2c-ff683437c936

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva_a22_original_ruinstopped_prepayment_compact_allband
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
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ) (q : ℝ) (a b : ℕ → ℝ)
    (hcover : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      ∃ N : ℕ, ∀ n ≥ N, y ∈ Icc (a n) (b n))
    (c d : ℝ) (hc : 0 < c) (hcd : c ≤ d)
    (hcC : ENNReal.ofReal c < C) (hdC : ENNReal.ofReal d < C) :
    let Y : ℝ≥0 → Ω → ℝ := fun t ω =>
      Function.leftLim (fun r : ℝ≥0 =>
        x + X.X r ω - rightLimit D r ω) t
    ∃ N : ℕ, ∀ n ≥ N, ∀ (S : ℝ≥0) (ω : Ω) (t : ℝ≥0) (z : ℝ),
      (t : ℝ≥0∞) ≤ min (ruinTime X x D ω) (S : ℝ≥0∞) →
      Y t ω ∈ Icc c d → z < 0 →
      (if (((t : ℝ≥0∞) ≤
          min (ruinTime X x D ω) (S : ℝ≥0∞) ∧
          Y t ω ∈ Icc (a n) (b n)) ∧ z < 0) then
        Real.exp (-(q * (t : ℝ))) * (w (Y t ω + z) - w (Y t ω))
      else 0) =
        Real.exp (-(q * (t : ℝ))) * (w (Y t ω + z) - w (Y t ω)) := by
  intro Y
  obtain ⟨N, hN⟩ :=
    avram_bva_a22_original_ruinstopped_prepayment_compact_allband
      X x C D hD a b hcover c d hc hcd hcC hdC
  refine ⟨N, ?_⟩
  intro n hn S ω t z ht hcompact hz
  have hb : Y t ω ∈ Icc (a n) (b n) :=
    hN n hn S ω t ht hcompact
  have hmask : ((t : ℝ≥0∞) ≤
      min (ruinTime X x D ω) (S : ℝ≥0∞) ∧
      Y t ω ∈ Icc (a n) (b n)) ∧ z < 0 :=
    ⟨⟨ht, hb⟩, hz⟩
  rw [if_pos hmask]
