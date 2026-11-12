-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger39_original_bounded_stop_discount_mesh_error_L1
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T12:03:13.669833+00:00
-- url     : https://prove2.me/submissions/2c9ce437-a43f-4301-87a2-b336dcd85785
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger38_original_bounded_stop_discount_mesh_error_L1
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The stopping-time ruin bound is unnecessary for the stronger open estimate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (hρbound : ∀ ω, ρ ω ≤ (n : ℝ≥0))
    (_hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let u : ℝ≥0 := ρ ω - Δ
      q * (Δ : ℝ) *
        (dividendMeasure D ω (Ioo (0 : ℝ) (ρ ω : ℝ))).toReal +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (ρ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (E m) P ∧ (∫ ω, E m ω ∂P) ≤ ε := by
  exact avram_gledger38_original_bounded_stop_discount_mesh_error_L1
    X hX x C D hD q hq n hn ρ hρstop hρbound
