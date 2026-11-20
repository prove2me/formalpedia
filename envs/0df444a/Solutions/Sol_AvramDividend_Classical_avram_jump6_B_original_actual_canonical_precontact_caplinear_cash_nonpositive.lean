-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_actual_canonical_precontact_caplinear_cash_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T17:16:01.618979+00:00
-- url     : https://prove2.me/submissions/3ea977d8-4b63-4c48-9ff1-fa457483c58a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    (∑ i ∈ Finset.range ((n + 1) * (j + 1)),
      ((∫⁻ s in Ioc (v i : ℝ) (v (i + 1) : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal +
        Real.exp (-(q * (v i : ℝ))) *
          (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
           V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤ 0 := by
  intro v V
  have hMon : Monotone (fun i : ℕ =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t) := by
    intro a b hab
    dsimp
    gcongr
  have hPre : ∀ i < (n + 1) * (j + 1),
      (min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t) = 0 ∨
        ((min (((i + 1 : ℕ) : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t : ℝ≥0) : ℝ≥0∞) <
          ruinTime X x D ω := by
    intro i hi
    right
    exact lt_of_le_of_lt (ENNReal.coe_le_coe.mpr (min_le_right _ _)) ht
  simpa only using
    (avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
      X x q hq C hC w hw_cont hw_smooth hw_grad D hD ω
      (fun i => min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t)
      hMon ((n + 1) * (j + 1)) hPre)
