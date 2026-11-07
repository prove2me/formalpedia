-- Prove2me | solution 20 for AvramDividend.Classical.barrier_cstar_verification_upper_bounds
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T23:45:47.9766+00:00
-- url     : https://prove2.me/submissions/cd5cab55-75b9-4aa9-838e-f3b1faa0eb4e
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_bounded_variation
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_dividendValue_le_unbounded_variation
import Theorems.Thm_AvramDividend_Classical_local_verification_from_uniform_truncated_hjb_budget
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_zero_cstar_original_capped_optimality
import Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
import Theorems.Thm_AvramDividend_Classical_avram_sweep17_vcstar_positive_cap_interior_HJB
import Theorems.Thm_AvramDividend_Classical_avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
import Theorems.Thm_AvramDividend_Classical_avram_sweep19_vcstar_top_original_verification_hypotheses
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
    ((∀ y : ℝ, (cstar W).toReal < y →
       X.GeneratorIntegrable (vcstar W) y ∧
         X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
      ∀ x : ℝ, 0 ≤ x →
        valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) := by
  have hLocal
      (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
      (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
      (hw_neg : ∀ y < 0, w y = 0)
      (hw_smooth : (¬ X.BoundedVariation → ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
        (X.BoundedVariation → ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
      (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
      (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
      (C = ⊤ → ∀ x : ℝ, 0 ≤ x → valueFunction X q x ≤ ENNReal.ofReal (w x)) := by
    apply local_verification_from_uniform_truncated_hjb_budget X q w C
    intro x hx hxc D hD n
    by_cases hBV : X.BoundedVariation
    · exact admissible_cap_truncated_dividendValue_le_bounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg (hw_smooth.2 hBV) hw_hjb x hx hxc D hD (n : ℝ) (by positivity)
    · exact admissible_cap_truncated_dividendValue_le_unbounded_variation
        X hX hBV q hq w C hC hw_cont hw0 hw_neg (hw_smooth.1 hBV) hw_hjb x hx hxc D hD (n : ℝ) (by positivity)
  have hUpper :
      (∀ x : ℝ, 0 ≤ x → valueFunctionLe X q (cstar W) x ≤ ENNReal.ofReal (vcstar W x)) ∧
      ((∀ y : ℝ, (cstar W).toReal < y → X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) →
        ∀ x : ℝ, 0 ≤ x → valueFunction X q x ≤ ENNReal.ofReal (vcstar W x)) := by
    constructor
    · by_cases hzero : cstar W = 0
      · intro x hx
        exact le_of_eq
          (avram_sweep16_zero_cstar_original_capped_optimality
            X hX q hq W hW hzero x hx)
      · have hcpos : (0 : ℝ≥0∞) < cstar W :=
          lt_of_le_of_ne bot_le (Ne.symm hzero)
        obtain ⟨hcont, hnonneg, hneg, hsmooth⟩ :=
          vcstar_local_verification_regular_of_positive_cstar
            X hX q hq W hW hc hcpos h_smooth
        have hhjb := avram_sweep17_vcstar_positive_cap_interior_HJB
          X hX q hq W hW hc hcpos h_smooth
        have hlocal := (hLocal (vcstar W) (cstar W)
          hcpos hcont hnonneg hneg hsmooth hhjb).1
        exact avram_sweep16_finite_cstar_local_cap_upper_yields_global_upper
          X hX q hq W hW hc h_smooth hlocal
    · intro hgen
      obtain ⟨hcont, hnonneg, hneg, hsmooth, hhjb⟩ :=
        avram_sweep19_vcstar_top_original_verification_hypotheses
          X hX q hq W hW hc h_smooth hgen
      have htop : (0 : ℝ≥0∞) < ⊤ := by simp
      exact (hLocal
        (vcstar W) ⊤ htop hcont hnonneg hneg hsmooth hhjb).2 rfl
  exact hUpper
