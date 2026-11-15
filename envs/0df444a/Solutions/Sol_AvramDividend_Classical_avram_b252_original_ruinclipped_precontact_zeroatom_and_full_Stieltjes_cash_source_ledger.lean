-- Prove2me | solution 1 for AvramDividend.Classical.avram_b252_original_ruinclipped_precontact_zeroatom_and_full_Stieltjes_cash_source_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:15:55.973286+00:00
-- url     : https://prove2.me/submissions/0f866a24-b5ff-48f5-82b3-10ceb879ef7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b248_original_ruinclipped_precontact_physical_full_Stieltjes_cash_source_ledger
import Theorems.Thm_AvramDividend_Classical_avram_b251_original_ruinclipped_mixed_allcap_initial_real_Stieltjes_dividend_atom_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
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
    (hPre : ∀ i ∈ Finset.range m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
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
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
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
  change
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
    e m * V (Y m) + (Finset.range m).sum cash ≤
    V x + (Finset.range m).sum (fun i =>
      e (i + 1) * V (Z i) - e i * V (Y i)) +
    (Finset.range m).sum err
  have hGrid :=
    avram_b248_original_ruinclipped_precontact_physical_full_Stieltjes_cash_source_ledger
      X x q hq C hC w hw_cont hw_smooth hw_grad D hD σ n m ω hPre
  change e m * V (Y m) + (Finset.range m).sum cash ≤
    e 0 * V (Y 0) + (Finset.range m).sum (fun i =>
      e (i + 1) * V (Z i) - e i * V (Y i)) +
    (Finset.range m).sum err at hGrid
  have hInit :=
    avram_b251_original_ruinclipped_mixed_allcap_initial_real_Stieltjes_dividend_atom_budget
      X x q hq C w hw_cont hw_smooth hw_grad D hD ω
  change
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
    V (x - rightLimit D 0 ω) ≤ V x at hInit
  have hv0 : v 0 = 0 := by simp [v]
  have he0 : e 0 = 1 := by simp [e, hv0]
  have hy0 : Y 0 = x - rightLimit D 0 ω := by
    simp only [Y, hv0, X.X_zero, add_zero]
  rw [he0, hy0] at hGrid
  linarith only [hGrid, hInit]
