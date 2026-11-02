-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_separate_gradient_right_atom_control
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T08:54:49.425771+00:00
-- url     : https://prove2.me/submissions/57f260d1-b582-4a18-94e7-3c9984823a1b

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_rightJump_decomposition
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

/-- The BV and corrected UBV separate gradient hypotheses control each
    actual pre-ruin right-payment atom, including the initial atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth :
      (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)) := by
  intro ω t ht
  have hs : IsDividendStrategy 𝓕 D := hD.1.1
  have hd : 0 ≤ rightLimit D t ω - D t ω :=
    (postPaymentReserve_rightJump_decomposition X x D hs ω t).1
  have hpaid :
      rightLimit D t ω - D t ω ≤ riskProcess X x D t ω :=
    hD.1.2 ω t ht
  have hcap : ENNReal.ofReal (riskProcess X x D t ω) ≤ C := by
    by_cases hzero : t = 0
    · subst t
      have hD0 : D 0 ω = 0 := hs.1 ω
      have hX0 : X.X 0 ω = 0 := X.X_zero ω
      simpa only [riskProcess, hX0, hD0, sub_zero, add_zero] using hxc
    · have htpos : 0 < t :=
        lt_of_le_of_ne (zero_le : (0 : ℝ≥0) ≤ t) (Ne.symm hzero)
      exact hD.2 ω t htpos
  let a : ℝ :=
    riskProcess X x D t ω - (rightLimit D t ω - D t ω)
  let b : ℝ := riskProcess X x D t ω
  have ha : 0 ≤ a := by dsimp [a]; linarith
  have hab : a ≤ b := by dsimp [a, b]; linarith
  have hb : ENNReal.ofReal b ≤ C := hcap
  have hsec : b - a ≤ w b - w a := by
    by_cases hBV : X.BoundedVariation
    · exact avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont (hw_smooth.2 hBV) hw_grad a b ha hab hb
    · exact avram_wave3_04_ubv_C2_gradient_secant_closed_all_caps
        C w hw_cont (hw_smooth.1 hBV) hw_grad a b ha hab hb
  dsimp [a, b] at hsec
  linarith
