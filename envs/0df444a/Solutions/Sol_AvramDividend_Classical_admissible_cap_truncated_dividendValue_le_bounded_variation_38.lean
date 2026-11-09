-- Prove2me | solution 38 for AvramDividend.Classical.admissible_cap_truncated_dividendValue_le_bounded_variation
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-08T14:37:38.643221+00:00
-- url     : https://prove2.me/submissions/48c88c0f-82c0-47d8-920a-e4c6fa42567c
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_local_verification_stochastic_core_side_conditions
import Theorems.Thm_AvramDividend_Classical_admissible_cap_truncated_zero_horizon_hjb_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_strict_HJB_to_signed_full
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_positive_horizon_signed_HJB_to_closed_cash

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      ENNReal.ofReal (w x) := by
  have hw_smooth_conj :
      ((¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})) := by
    constructor
    · intro hNot
      exact False.elim (hNot hBV)
    · intro _
      exact hw_smooth
  have hSide :=
    AvramDividend.Classical.local_verification_stochastic_core_side_conditions
      X q w C hw_cont hw0 hw_smooth_conj hw_hjb x hxc D hD
  obtain ⟨hGen, hGrad, hNonneg, hJump⟩ := hSide
  by_cases hT0 : T = 0
  · subst hT0
    exact AvramDividend.Classical.admissible_cap_truncated_zero_horizon_hjb_bound
      X q x w C hw_cont hw0 hw_smooth_conj hw_hjb D hD hxc
  · have hTpos : 0 < T := lt_of_le_of_ne hT (fun h => hT0 h.symm)
    have hPre :=
      AvramDividend.Classical.avram_p3_bv_original_positive_horizon_stopped_prebudget_HJB
        X hX hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth
        hGen hGrad x hx hxc D hD hNonneg hJump T hT hTpos
    have hClosed :=
      AvramDividend.Classical.avram_p3_bv_strict_HJB_to_signed_full
        X hBV q hq w C hC hw_cont hw0 hw_neg hw_smooth hGrad x D hD hJump T hT hTpos hPre
    have hq_nonneg : 0 ≤ q := le_of_lt hq
    exact
      AvramDividend.Classical.avram_bv_env3_original_positive_horizon_signed_HJB_to_closed_cash
      X hBV q hq_nonneg w C hC hw_cont hw0 hw_neg hw_smooth hGrad x hx hxc D hD
      T hT hTpos hClosed
