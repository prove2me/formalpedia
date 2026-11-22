-- Prove2me | solution 1 for AvramDividend.Classical.avram_oai_original_positive_clock_cash_lastmesh_L1_auto_20261122
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T21:10:43.413901+00:00
-- url     : https://prove2.me/submissions/ecb75748-2c81-4e88-bb04-7bc48f79bc59

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q)
    (n : ℕ) (hn : 0 < n) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (σ : ℕ → Ω → ℝ≥0)
    (hσstop : ∀ k, IsStoppingTime 𝓕.rightCont
      (fun ω => (σ k ω : WithTop ℝ≥0)))
    (hσle : ∀ k ω, σ k ω ≤ τ ω) :
    ∀ k : ℕ,
      let E : ℕ → Ω → ℝ := fun m ω =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let u : ℝ≥0 := σ k ω - Δ
        q * (Δ : ℝ) *
          (dividendMeasure D ω (Ioo (0 : ℝ) (σ k ω : ℝ))).toReal +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
          Ioo (u : ℝ) (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m : ℕ, N ≤ m →
        Integrable (E m) P ∧ (∫ ω, |E m ω| ∂P) ≤ ε  := by
  intro k E
  have hτext (ω : Ω) :
      (τ ω : ℝ≥0∞) = min (ruinTime X x D ω) (n : ℝ≥0∞) :=
    avram_p4_d_dividend_original_ruin_truncated_NNReal_clock_exact_min_in_extended_time
      X x D n τ hτeq ω
  have hρbound : ∀ ω, σ k ω ≤ (n : ℝ≥0) := by
    intro ω
    have hσext : (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by
      exact_mod_cast hσle k ω
    have hνext : (σ k ω : ℝ≥0∞) ≤ (n : ℝ≥0∞) := by
      calc
        (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := hσext
        _ = min (ruinTime X x D ω) (n : ℝ≥0∞) := hτext ω
        _ ≤ (n : ℝ≥0∞) := min_le_right _ _
    exact_mod_cast hνext
  have hρruin : ∀ ω, (σ k ω : ℝ≥0∞) ≤ ruinTime X x D ω := by
    intro ω
    calc
      (σ k ω : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) := by
        exact_mod_cast hσle k ω
      _ = min (ruinTime X x D ω) (n : ℝ≥0∞) := hτext ω
      _ ≤ ruinTime X x D ω := min_le_left _ _
  simpa only [E] using
    (avram_pj_workerC_original_bounded_stopped_discount_cash_mesh_absolute_error_L1_eventual
      X hX x C D hD q hq n hn (σ k) (hσstop k) hρbound hρruin)
