-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T08:35:46.221854+00:00
-- url     : https://prove2.me/submissions/373ec524-cfee-4737-b6f4-582a339f4388

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger39_original_bounded_stop_discount_mesh_error_L1
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

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
    (hρruin : ∀ ω, (ρ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
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
      Integrable (E m) P ∧ (∫ ω, |E m ω| ∂P) ≤ ε := by
  intro E ε hε
  obtain ⟨k, hk⟩ :=
    AvramDividend.Classical.avram_gledger39_original_bounded_stop_discount_mesh_error_L1
      X hX x C D hD q hq n hn ρ hρstop hρbound hρruin ε hε
  refine ⟨k, ?_⟩
  intro m hm
  obtain ⟨hI, hUpper⟩ := hk m hm
  refine ⟨hI, ?_⟩
  have hENonneg : ∀ ω, 0 ≤ E m ω := by
    intro ω
    dsimp [E]
    positivity
  have hAbs : (fun ω => |E m ω|) = E m := by
    funext ω
    exact abs_of_nonneg (hENonneg ω)
  rw [hAbs]
  exact hUpper
