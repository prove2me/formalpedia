-- Prove2me | solution 1 for AvramDividend.Classical.avram_b248_original_ruinclipped_precontact_physical_full_Stieltjes_cash_source_ledger
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:36:03.568203+00:00
-- url     : https://prove2.me/submissions/e54873ea-2c08-465e-9eb6-cd7bd23f6d10

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
import Theorems.Thm_AvramDividend_Classical_avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
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
    e m * V (Y m) + (Finset.range m).sum cash ≤
      e 0 * V (Y 0) +
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
  change e m * V (Y m) + (Finset.range m).sum cash ≤
    e 0 * V (Y 0) +
    (Finset.range m).sum (fun i =>
      e (i + 1) * V (Z i) - e i * V (Y i)) +
    (Finset.range m).sum err
  have hCell (i : ℕ) (hi : i ∈ Finset.range m) :
      cash i + e (i + 1) * (V (Y (i + 1)) - V (Z i)) ≤
        err i := by
    have hv : v i ≤ v (i + 1) := by
      dsimp [v]
      gcongr <;> omega
    have h :=
      avram_b241_original_ruinclipped_allcap_physical_cash_left_to_right_discount_mesh_correction
        X x q hq C hC w hw_cont hw_smooth hw_grad
        D hD ω (v i) (v (i + 1)) hv (hPre i hi)
    change cash i + e (i + 1) * (V (Y (i + 1)) - V (Z i)) ≤ err i at h
    exact h
  have hSum :
      (Finset.range m).sum (fun i =>
        cash i + e (i + 1) * (V (Y (i + 1)) - V (Z i))) ≤
      (Finset.range m).sum err := by
    exact Finset.sum_le_sum (fun i hi => hCell i hi)
  have hTel :=
    avram_b238_original_ruinclipped_finiteactivity_physical_stopped_source_postdividend_telescope
      X x q V D σ n m ω
  change e m * V (Y m) - e 0 * V (Y 0) =
    (Finset.range m).sum (fun i =>
      (e (i + 1) * V (Z i) - e i * V (Y i)) +
      e (i + 1) * (V (Y (i + 1)) - V (Z i))) at hTel
  rw [Finset.sum_add_distrib] at hTel hSum
  linarith only [hTel, hSum]
