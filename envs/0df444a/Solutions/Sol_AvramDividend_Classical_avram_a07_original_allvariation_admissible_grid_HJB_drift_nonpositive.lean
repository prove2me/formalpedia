-- Prove2me | solution 1 for AvramDividend.Classical.avram_a07_original_allvariation_admissible_grid_HJB_drift_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T22:37:48.047065+00:00
-- url     : https://prove2.me/submissions/9120a854-3cd0-4a3d-bb7d-ea97715c3eb2

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Admissibility automatically supplies the nonnegative grid dividend increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) 
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (u : ℕ → ℝ≥0) (hu : Monotone u)
    (cells : Finset ℕ)
    (hregion : ∀ i ∈ cells,
      0 < riskProcess X x D (u i) ω ∧
        ENNReal.ofReal (riskProcess X x D (u i) ω) < C) :
    (∑ i ∈ cells,
      Real.exp (-(q * (u i : ℝ))) *
        (((u (i + 1) : ℝ) - (u i : ℝ)) *
          (X.generator w (riskProcess X x D (u i) ω) -
            q * w (riskProcess X x D (u i) ω)) +
        (D (u (i + 1)) ω - D (u i) ω) *
          (1 - deriv w (riskProcess X x D (u i) ω)))) ≤ 0 := by
  have hmon : Monotone (fun t : ℝ≥0 => D t ω) :=
    hD.1.1.2.1 ω
  have hdiv : ∀ i ∈ cells,
      D (u i) ω ≤ D (u (i + 1)) ω := by
    intro i hi
    exact hmon (hu (Nat.le_succ i))
  apply Finset.sum_nonpos
  intro i hi
  let y : ℝ := riskProcess X x D (u i) ω
  have hpos : 0 < y := (hregion i hi).1
  have hcap : ENNReal.ofReal y < C := (hregion i hi).2
  have hgen : X.generator w y - q * w y ≤ 0 :=
    (hw_gen y hpos hcap).2
  have hderiv : 1 - deriv w y ≤ 0 :=
    sub_nonpos.mpr (hw_grad y hpos hcap)
  have hclock : (u i : ℝ) ≤ (u (i + 1) : ℝ) :=
    NNReal.coe_le_coe.mpr (hu (Nat.le_succ i))
  have htime : 0 ≤ (u (i + 1) : ℝ) - (u i : ℝ) :=
    sub_nonneg.mpr hclock
  have hcash : 0 ≤ D (u (i + 1)) ω - D (u i) ω :=
    sub_nonneg.mpr (hdiv i hi)
  have hleft : ((u (i + 1) : ℝ) - (u i : ℝ)) *
      (X.generator w y - q * w y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos htime hgen
  have hright :
      (D (u (i + 1)) ω - D (u i) ω) *
        (1 - deriv w y) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hcash hderiv
  have hsum : ((u (i + 1) : ℝ) - (u i : ℝ)) *
      (X.generator w y - q * w y) +
      (D (u (i + 1)) ω - D (u i) ω) *
        (1 - deriv w y) ≤ 0 :=
    add_nonpos hleft hright
  simpa only [y] using
    mul_nonpos_of_nonneg_of_nonpos
      (le_of_lt (Real.exp_pos (-(q * (u i : ℝ))))) hsum
