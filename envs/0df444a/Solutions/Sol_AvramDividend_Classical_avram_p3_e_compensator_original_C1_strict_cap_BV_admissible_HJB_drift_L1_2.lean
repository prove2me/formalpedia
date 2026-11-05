-- Prove2me | solution 2 for AvramDividend.Classical.avram_p3_e_compensator_original_C1_strict_cap_BV_admissible_HJB_drift_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T17:31:49.091851+00:00
-- url     : https://prove2.me/submissions/ae888651-a897-4ebf-be48-1aed61b3b8e3

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
import Theorems.Thm_AvramDividend_Classical_avram_p3_e_compensator_original_BV_admissible_HJB_drift_L1_from_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
{Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
{𝓕 : Filtration ℝ≥0 mΩ}
(X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
(T : ℝ≥0) (x : ℝ) (C : ℝ≥0∞)
(D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
(w : ℝ → ℝ) (hw_cont : ContinuousOn w (Set.Ici 0))
(hw_neg : ∀ y < 0, w y = 0)
(q : ℝ) (hq : 0 ≤ q)
(a b : ℝ) (ha : 0 < a) (ha2 : a ≤ 2)
(hab : a ≤ b) (hbC : ENNReal.ofReal b < C)
(hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
(E : Set (ℝ≥0 × Ω)) (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
(hEregion : ∀ p ∈ E, Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1 ∈ Set.Icc a b) :
Integrable (fun p : ℝ≥0 × Ω => if p ∈ E then Real.exp (-(q * (p.1 : ℝ))) *
    (X.drift * deriv w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) +
     (∫ z in Set.Iio (0 : ℝ),
        w ((Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) + z) - w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1) ∂X.ν) -
     q * w (Function.leftLim (fun v : ℝ≥0 => x + X.X v p.2 - rightLimit D v p.2) p.1)) else 0)
  ((((volume : Measure ℝ).restrict (Set.Icc 0 (T : ℝ))).map Real.toNNReal).prod P)  := by
  obtain ⟨L, hL, hLip⟩ :=
    avram_p3_e_compensator_original_strict_cap_C1_Lipschitz
      C w a b ha hab hbC hw_smooth
  obtain ⟨R, hR, hWbound⟩ :=
    avram_p3_e_compensator_negative_jump_halfline_bound_of_continuity
      w hw_cont hw_neg b
  obtain ⟨A, hA, hDeriv⟩ :=
    avram_p3_e_compensator_original_strict_cap_C1_derivative_compact_bound
      C w a b ha hab hbC hw_smooth
  exact avram_p3_e_compensator_original_BV_admissible_HJB_drift_L1_from_source
    X hBV T x C D hD w hw_cont hw_neg q hq a b L R A
    ha ha2 hab hL hR hA hLip hWbound hDeriv E hEm hEregion
