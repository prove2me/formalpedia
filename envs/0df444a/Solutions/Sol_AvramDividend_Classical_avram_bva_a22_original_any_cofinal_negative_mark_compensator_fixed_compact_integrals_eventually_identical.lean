-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva_a22_original_any_cofinal_negative_mark_compensator_fixed_compact_integrals_eventually_identical
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:18.010651+00:00
-- url     : https://prove2.me/submissions/de2a3283-87fe-479f-a34d-b3986f5ae7b9

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
    ∃ N : ℕ, ∀ n ≥ N, ∀ (S : ℝ≥0)
      (μ : Measure ((ℝ≥0 × Ω) × ℝ)),
      (∫ p, if
        (((p.1.1 : ℝ≥0∞) ≤ min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧
          Y p.1.1 p.1.2 ∈ Icc c d ∧ p.2 < 0) ∧
          Y p.1.1 p.1.2 ∈ Icc (a n) (b n)) then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
        else 0 ∂μ) =
      (∫ p, if
        ((p.1.1 : ℝ≥0∞) ≤ min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧
          Y p.1.1 p.1.2 ∈ Icc c d ∧ p.2 < 0) then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1.1 p.1.2 + p.2) - w (Y p.1.1 p.1.2))
        else 0 ∂μ) := by
  intro Y
  obtain ⟨N, hN⟩ :=
    avram_bva_a22_original_ruinstopped_prepayment_compact_allband
      X x C D hD a b hcover c d hc hcd hcC hdC
  refine ⟨N, ?_⟩
  intro n hn S μ
  apply integral_congr_ae
  filter_upwards [] with p
  by_cases hActive :
      (p.1.1 : ℝ≥0∞) ≤
        min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧
      Y p.1.1 p.1.2 ∈ Icc c d ∧ p.2 < 0
  · have hb : Y p.1.1 p.1.2 ∈ Icc (a n) (b n) :=
      hN n hn S p.1.2 p.1.1 hActive.1 hActive.2.1
    rw [if_pos ⟨hActive, hb⟩, if_pos hActive]
  · have hFail : ¬
        (((p.1.1 : ℝ≥0∞) ≤
            min (ruinTime X x D p.1.2) (S : ℝ≥0∞) ∧
          Y p.1.1 p.1.2 ∈ Icc c d ∧ p.2 < 0) ∧
          Y p.1.1 p.1.2 ∈ Icc (a n) (b n)) :=
      fun h => hActive h.1
    rw [if_neg hFail, if_neg hActive]
