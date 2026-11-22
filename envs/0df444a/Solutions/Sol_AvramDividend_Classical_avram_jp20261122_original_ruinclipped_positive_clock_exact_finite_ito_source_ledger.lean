-- Prove2me | solution 1 for AvramDividend.Classical.avram_jp20261122_original_ruinclipped_positive_clock_exact_finite_ito_source_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T22:06:50.760452+00:00
-- url     : https://prove2.me/submissions/7ed7e974-7236-4923-ab6b-cfb76809099d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (σ : Ω → ℝ≥0) (n : ℕ)
    (F : Ω → ℝ)
    (hFsource : ∀ ω, F ω =
      Real.exp (-(q * (σ ω : ℝ))) *
        w (if σ ω = 0 ∨
              (σ ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ ω) ω - rightLimit D (σ ω) ω
          else riskProcess X x D (σ ω) ω) +
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
        ∂(dividendMeasure D ω)).toReal) :
    ∀ (m : ℕ) (ω : Ω),
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
      let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
      let Y : ℕ → ℝ := fun i =>
        x + X.X (v i) ω - rightLimit D (v i) ω
      let Z : ℕ → ℝ := fun i =>
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
      let W : ℝ := if σ ω = 0 ∨
        (σ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (σ ω) ω - rightLimit D (σ ω) ω
        else riskProcess X x D (σ ω) ω
      let Cash : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      F ω - w x =
        (∑ i ∈ Finset.range m,
          ((e (i + 1) * w (Z i) - e i * w (Y i)) +
            e (i + 1) * (w (Y (i + 1)) - w (Z i)))) +
        (Real.exp (-(q * (σ ω : ℝ))) * w W - e m * w (Y m)) +
        (e 0 * w (Y 0) - w x) + Cash := by
  classical
  intro m ω
  have ht :=
    avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
      X x q w D σ n m ω
  dsimp only at ht ⊢
  rw [hFsource ω]
  rw [← ht]
  ring
