-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva71_original_arbitrary_real_horizon_clipped_ruin_cash_error_certificate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T17:38:59.85179+00:00
-- url     : https://prove2.me/submissions/4954a42d-d0c8-4fed-8042-e549a412676a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bva70_original_real_horizon_strict_clipped_ruin_cash_mesh_error_L1_vanish
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (q : ℝ) (hq : 0 < q) (T : ℝ≥0) :
    ∃ n : ℕ, 0 < n ∧ T ≤ (n : ℝ≥0) ∧
    (let ρ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let E : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ := (n : ℝ) / ((m : ℝ) + 2)
      let F : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iio (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      let T : ℝ :=
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
            Ioo ((ρ ω : ℝ) - Δ) (ρ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal
      q * Δ * Real.exp (q * (n : ℝ)) * F + T
    (∀ m : ℕ, Integrable (E m) P) ∧
    Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (nhds (0 : ℝ))) := by
  let n : ℕ := ⌈T⌉₊ + 1
  have hn : 0 < n := by
    dsimp [n]
    omega
  have hBound : T ≤ (n : ℝ≥0) := by
    dsimp [n]
    calc
      T ≤ (⌈T⌉₊ : ℝ≥0) := Nat.le_ceil T
      _ ≤ ((⌈T⌉₊ + 1 : ℕ) : ℝ≥0) := by
        exact_mod_cast Nat.le_succ (⌈T⌉₊)
  refine ⟨n, hn, hBound, ?_⟩
  exact
    avram_bva70_original_real_horizon_strict_clipped_ruin_cash_mesh_error_L1_vanish
      X hX x C D hD q hq n hn T hBound

