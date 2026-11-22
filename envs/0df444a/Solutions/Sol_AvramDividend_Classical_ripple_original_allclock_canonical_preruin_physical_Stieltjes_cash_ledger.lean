-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_allclock_canonical_preruin_physical_Stieltjes_cash_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T17:26:44.348538+00:00
-- url     : https://prove2.me/submissions/010dff7e-02be-4d56-8d65-a093b91f12e5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ripple_original_strict_preruin_full_discounted_Stieltjes_cash
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (hC : 0 < C)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0) (n m : ℕ) (ω : Ω)
    (hσpos : 0 < σ ω)
    (hσle : (σ ω : ℝ≥0∞) ≤ ruinTime X x D ω) (j : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω - σ ω / ((j : ℝ≥0) + 1))
    let e : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let Y : ℕ → ℝ := fun i =>
      x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    let cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal
    let err : ℕ → ℝ := fun i =>
      (e i - e (i + 1)) * (V (Z i) - V (Y (i + 1)))
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
      e m * V (Y m) + (Finset.range m).sum cash ≤
      V x +
      (Finset.range m).sum (fun i =>
        e (i + 1) * V (Z i) - e i * V (Y i)) +
      (Finset.range m).sum err := by
  classical
  have hden : (0 : ℝ≥0) < (j : ℝ≥0) + 1 := by positivity
  have hwidth : (0 : ℝ≥0) < σ ω / ((j : ℝ≥0) + 1) :=
    div_pos hσpos hden
  have hLt : σ ω - σ ω / ((j : ℝ≥0) + 1) < σ ω :=
    tsub_lt_self hσpos hwidth
  have hSurvive :
      ((σ ω - σ ω / ((j : ℝ≥0) + 1) : ℝ≥0) : ℝ≥0∞) <
        ruinTime X x D ω :=
    (ENNReal.coe_lt_coe.mpr hLt).trans_le hσle
  simpa only using
    (ripple_original_strict_preruin_full_discounted_Stieltjes_cash
      X x q hq C hC w hw_cont hw_smooth hw_grad D hD
      (fun η => σ η - σ η / ((j : ℝ≥0) + 1))
      n m ω hSurvive)
