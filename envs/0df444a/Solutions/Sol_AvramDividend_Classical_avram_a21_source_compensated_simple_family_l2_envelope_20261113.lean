-- Prove2me | solution 1 for AvramDividend.Classical.avram_a21_source_compensated_simple_family_l2_envelope_20261113
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:16:35.634191+00:00
-- url     : https://prove2.me/submissions/335952bd-eaf3-4bc4-bcdc-3bf0ae8e02c3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a20_original_negative_borel_count_compensator_square_envelope
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_bounded_compensated_mark_ae_count_rate_domination_20261113
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- A single source-physical squared-integrable count-and-rate envelope
dominates every compensated real simple-mark approximant. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (T : ℝ≥0) (S : Set ℝ)
    (hS : MeasurableSet S) (hNeg : S ⊆ Iio (0 : ℝ))
    (f : ℕ → SimpleFunc ℝ ℝ)
    (hBound : ∀ k z, z ∈ S → |f k z| ≤ 1) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let D : Ω → ℝ := fun ω =>
      (NX ω (Ioc 0 T ×ˢ S)).toReal +
        (((T : ℝ≥0∞) * X.ν S).toReal)
    let Z : ℕ → Ω → ℝ := fun k ω =>
      (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
        (T : ℝ) * (∫ z in S, f k z ∂X.ν)
    Integrable (fun ω => (D ω)^2) P ∧
      (∀ k, ∀ᵐ ω ∂P, ‖Z k ω‖ ≤ D ω) := by
  let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u, X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  let D : Ω → ℝ := fun ω =>
    (NX ω (Ioc 0 T ×ˢ S)).toReal +
      (((T : ℝ≥0∞) * X.ν S).toReal)
  let Z : ℕ → Ω → ℝ := fun k ω =>
    (∫ p in (Ioc 0 T ×ˢ S), f k p.2 ∂NX ω) -
      (T : ℝ) * (∫ z in S, f k z ∂X.ν)
  constructor
  · exact avram_a20_original_negative_borel_count_compensator_square_envelope
      X hFinite T S hS hNeg
  · intro k
    exact avram_a21_original_bounded_compensated_mark_ae_count_rate_domination_20261113
      X hFinite T S hS hNeg (f k) (f k).measurable
      (fun z hz => hBound k z hz)
