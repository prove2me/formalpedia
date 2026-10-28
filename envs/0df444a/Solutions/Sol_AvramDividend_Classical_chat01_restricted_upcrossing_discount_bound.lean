-- Prove2me | solution 1 for AvramDividend.Classical.chat01_restricted_upcrossing_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:44:27.048321+00:00
-- url     : https://prove2.me/submissions/af90ee6c-c38a-4de3-a47e-5bf334073d88

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Any event restricting finite first-upcrossing inherits the positive-root
    exponential discount bound, with no assumptions on the extra killing. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)}) :
    (∫⁻ ω, A.indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X z ω))))) ω ∂P) ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by
  calc
    _ ≤ (∫⁻ ω, ({ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)}).indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X z ω))))) ω ∂P) := by
        apply lintegral_mono
        intro ω
        by_cases hmem : ω ∈ A
        · have hup : ω ∈ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)} :=
            hA hmem
          simp only [Set.indicator_of_mem hmem, Set.indicator_of_mem hup]
          exact le_rfl
        · rw [Set.indicator_of_notMem hmem]
          exact bot_le
    _ ≤ _ := by
      calc
        (∫⁻ ω, ({ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)}).indicator
          (fun ω => ENNReal.ofReal
            (Real.exp (-(q * ENNReal.toReal
              (twoSidedExitUpTimeCorrected X z ω))))) ω ∂P) =
          (∫⁻ ω, if twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
            then ENNReal.ofReal
              (Real.exp (-(q * ENNReal.toReal
                (twoSidedExitUpTimeCorrected X z ω))))
            else 0 ∂P) := by
              apply lintegral_congr
              intro ω
              by_cases hfin : twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)
              · have hmem : ω ∈ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)} := hfin
                rw [Set.indicator_of_mem hmem, if_pos hfin]
              · have hnmem : ω ∉ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)} := hfin
                rw [Set.indicator_of_notMem hnmem, if_neg hfin]
        _ ≤ _ :=
          levy_positive_root_unrestricted_upcrossing_discount_bound
            X q hq φ hφ hroot z hz
