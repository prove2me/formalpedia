-- Prove2me | solution 1 for AvramDividend.Classical.avram_b251_original_ruinclipped_mixed_allcap_initial_real_Stieltjes_dividend_atom_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T21:47:00.381578+00:00
-- url     : https://prove2.me/submissions/aa82024d-a282-4288-85ed-611b0bba2f33

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ω : Ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z else
      if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)).toReal +
    V (x - rightLimit D 0 ω) ≤ V x := by
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z else
    if z ≤ C.toReal then w z else w C.toReal + (z - C.toReal)
  have hVtop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro h z
    simp [V, h]
  have hVfinite : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro h z
    simp [V, h]
  have h := avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
    X x C q hq w V hw_cont hw_smooth hw_grad
    hVtop hVfinite D hD ω (0 : ℝ≥0) (Or.inl rfl)
  change
    (∫⁻ t in Icc (0 : ℝ) (0 : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal +
    (V (x + X.X 0 ω - rightLimit D 0 ω) -
     V (x + X.X 0 ω)) ≤ 0 at h
  rw [X.X_zero ω] at h
  simp only [add_zero] at h
  linarith
