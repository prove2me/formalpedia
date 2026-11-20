-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_original_clipped_precontact_caplinear_signed_cash_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-19T07:20:47.970074+00:00
-- url     : https://prove2.me/submissions/3cf55199-da37-40c0-b945-7c8fccc228f1

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
    (hClock : t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω)
    (n j : ℕ) :
    let v : ℕ → ℝ≥0 := fun i =>
      min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
    let m : ℕ := (n + 1) * (j + 1)
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    (∑ i ∈ Finset.range m,
      ((∫⁻ t in Ioc (v i : ℝ) (v (i + 1) : ℝ),
         ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)).toReal +
       Real.exp (-(q * (v i : ℝ))) *
        (V (x + X.X (v (i + 1)) ω - rightLimit D (v (i + 1)) ω) -
         V (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω)))) ≤ 0 := by
  dsimp only
  let v : ℕ → ℝ≥0 := fun i =>
    min ((i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)) t
  have hv : Monotone v := by
    intro a b hab
    dsimp [v]
    gcongr
  have hPre : ∀ i < (n + 1) * (j + 1),
      v (i + 1) = 0 ∨
        (v (i + 1) : ℝ≥0∞) < ruinTime X x D ω := by
    intro i hi
    rcases hClock with hz | hs
    . left
      simp [v, hz]
    . right
      have hvle : v (i + 1) ≤ t := by
        exact min_le_right _ _
      exact lt_of_le_of_lt (ENNReal.coe_le_coe.mpr hvle) hs
  exact avram_f6_true_original_caplinear_full_precontact_physical_grid_signed_cash_nonpos
    X x q hq C hC w hw_cont hw_smooth hw_grad D hD
    ω v hv ((n + 1) * (j + 1)) hPre
