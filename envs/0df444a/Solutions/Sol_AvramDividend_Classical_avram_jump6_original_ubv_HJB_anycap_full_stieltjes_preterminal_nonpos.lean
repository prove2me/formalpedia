-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_original_ubv_HJB_anycap_full_stieltjes_preterminal_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-21T18:57:46.079589+00:00
-- url     : https://prove2.me/submissions/4b822ff6-e978-445c-bf82-75dbca199b03

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Under the original unbounded-variation HJB max equation, the full physical
Stieltjes cash, including the initial payment atom and diffuse dividend part,
is dominated by the decrease of the cap-linear extended candidate value. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (hPre : T = 0 ∨ (T : ℝ≥0∞) < ruinTime X x D ω) :
    let V : ℝ → ℝ := fun z =>
      if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
       V (x + X.X T ω)) ≤ 0 := by
  have hw_smooth_one : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} :=
    hw_smooth.of_le (by norm_num)
  have hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y := by
    intro y hy hcap
    have hEq := (hw_hjb y hy hcap).2
    have hNeg : 1 - deriv w y ≤ 0 := by
      calc
        1 - deriv w y ≤
            max (X.generator w y - q * w y) (1 - deriv w y) :=
          le_max_right _ _
        _ = 0 := hEq
    linarith
  let V : ℝ → ℝ := fun z =>
    if C = ⊤ then w z
    else if z ≤ C.toReal then w z
    else w C.toReal + (z - C.toReal)
  have hTop : C = ⊤ → ∀ z : ℝ, V z = w z := by
    intro hTop z
    simp [V, hTop]
  have hFin : C ≠ ⊤ → ∀ z : ℝ,
      V z = if z ≤ C.toReal then w z
        else w C.toReal + (z - C.toReal) := by
    intro hFin z
    simp [V, hFin]
  change
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s)))
      ∂(dividendMeasure D ω)).toReal +
      (V (x + X.X T ω - rightLimit D T ω) -
       V (x + X.X T ω)) ≤ 0
  exact avram_wave6_05_any_cap_original_closed_full_stieltjes_signed_nonpos
    X x C q (le_of_lt hq) w V hw_cont hw_smooth_one hw_grad
    hTop hFin D hD ω T hPre

