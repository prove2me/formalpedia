-- Prove2me | solution 1 for AvramDividend.Classical.avram_f6_original_localised_full_precontact_physical_cash_rate_from_caplinear
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T22:17:14.194745+00:00
-- url     : https://prove2.me/submissions/0c06c050-b0dd-40e7-ae07-5b9ce4df4f97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f6_true_original_caplinear_precontact_right_discount_cash_error_exact
import Theorems.Thm_AvramDividend_Classical_avram_b254_original_ruinclipped_physical_postpayment_discount_gap_automatic_width
import Theorems.Thm_AvramDividend_Classical_avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (ω : Ω) (σ : Ω → ℝ≥0) (n m : ℕ)
    (hPre : ∀ i < m, let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω) (L a b : ℝ) (hL : 0 ≤ L)
    (hLip :
      let V : ℝ → ℝ := fun z =>
        if C = ⊤ then w z else
        if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
      ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, |V s - V t| ≤ L * |s - t|)
    (hBefore : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ∈ Icc a b) (hAfter : ∀ i < m,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let v : ℕ → ℝ≥0 := fun j => min ((j : ℝ≥0) * Δ) (σ ω)
      x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω ∈ Icc a b) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
    let V : ℝ → ℝ := fun z => if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    let E : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
    let Cash : ℕ → ℝ := fun i =>
      (∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
    (Finset.sum (Finset.range m) (fun i =>
      Cash i + E (i + 1) * (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤ q * (Δ : ℝ) * L *
        (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by
  let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
  let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (σ ω)
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else
    if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  let E : ℕ → ℝ := fun i => Real.exp (-(q * (v i : ℝ)))
  let B : ℕ → ℝ := fun i =>
    V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
    V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)
  let Cash : ℕ → ℝ := fun i =>
    (∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal
  have hv : Monotone v := by
    apply monotone_nat_of_le_succ; intro i
    exact (avram_b250_original_ruinclipped_true_physical_stopped_cell_width_and_clock_monotone
      n m (σ ω) i).1
  have hPre' : ∀ i < m,
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    intro i hi
    exact hPre i hi
  have hBase :=
    avram_f6_true_original_caplinear_precontact_right_discount_cash_error_exact
      X x q hq C hC w hw_cont hw_smooth hw_grad D hD ω v hv m hPre'
  change (Finset.sum (Finset.range m)
      (fun i => Cash i + E (i + 1) * B i)) ≤
    (Finset.sum (Finset.range m)
      (fun i => (E i - E (i + 1)) * (-(B i)))) at hBase
  have hAbs :=
    avram_b254_original_ruinclipped_physical_postpayment_discount_gap_automatic_width
      X x D hD.1.1 ω q hq V L hL a b hLip σ n m hBefore hAfter
  have hAbsB :
      (∑ i ∈ Finset.range m, (E i - E (i + 1)) * |B i|) ≤
      q * (Δ : ℝ) * L * (rightLimit D (v m) ω - rightLimit D (v 0) ω) := by
    convert hAbs using 1
    apply Finset.sum_congr rfl; intro i hi
    dsimp only [B]
    rw [abs_sub_comm]
  have hE : ∀ i : ℕ, 0 ≤ E i - E (i + 1) := by
    intro i
    have hvi : v i ≤ v (i + 1) := hv (Nat.le_succ i)
    have hvReal : (v i : ℝ) ≤ (v (i + 1) : ℝ) := by
      exact_mod_cast hvi
    have hProd := mul_le_mul_of_nonneg_left hvReal hq
    have hexp : E (i + 1) ≤ E i := by
      change Real.exp (-(q * (v (i + 1) : ℝ))) ≤ Real.exp (-(q * (v i : ℝ)))
      exact Real.exp_le_exp.mpr (by linarith)
    linarith
  change (Finset.sum (Finset.range m)
      (fun i => Cash i + E (i + 1) * B i)) ≤
    q * (Δ : ℝ) * L *
      (rightLimit D (v m) ω - rightLimit D (v 0) ω)
  calc
    (Finset.sum (Finset.range m)
      (fun i => Cash i + E (i + 1) * B i)) ≤
      (Finset.sum (Finset.range m)
        (fun i => (E i - E (i + 1)) * (-(B i)))) := hBase
    _ ≤ (Finset.sum (Finset.range m)
        (fun i => (E i - E (i + 1)) * |B i|)) := by
      apply Finset.sum_le_sum
      intro i hi
      exact mul_le_mul_of_nonneg_left (neg_le_abs (B i)) (hE i)
    _ ≤ q * (Δ : ℝ) * L *
          (rightLimit D (v m) ω - rightLimit D (v 0) ω) := hAbsB
