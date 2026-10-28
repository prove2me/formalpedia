-- Prove2me | solution 1 for AvramDividend.Classical.chat01_finite_horizon_upcrossing_discount_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:49:23.64621+00:00
-- url     : https://prove2.me/submissions/5e30597b-78bd-46f0-b762-6ea22706aeb9

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_levy_positive_root_unrestricted_upcrossing_discount_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- For a finite-horizon restricted first-upcrossing event, the constant
    discount at the time horizon is bounded by the Esscher tail weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (z : ℝ) (hz : 0 ≤ z) (A : Set Ω)
    (hA : A ⊆ {ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)})
    (t : ℝ) (htime : ∀ ω ∈ A, ENNReal.toReal (twoSidedExitUpTimeCorrected X z ω) ≤ t) :
    (∫⁻ ω, A.indicator (fun _ : Ω => ENNReal.ofReal (Real.exp (-(q * t)))) ω ∂P) ≤
      ENNReal.ofReal (Real.exp (-(φ * z))) := by
  calc
    _ ≤ (∫⁻ ω, A.indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X z ω))))) ω ∂P) := by
        apply lintegral_mono
        intro ω
        by_cases hmem : ω ∈ A
        · simp only [Set.indicator_of_mem hmem]
          apply ENNReal.ofReal_le_ofReal
          apply Real.exp_le_exp.mpr
          exact neg_le_neg (mul_le_mul_of_nonneg_left (htime ω hmem) hq.le)
        · simp only [Set.indicator_of_notMem hmem]
          exact le_rfl
    _ ≤ (∫⁻ ω, ({ω | twoSidedExitUpTimeCorrected X z ω < (⊤ : ℝ≥0∞)}).indicator
      (fun ω => ENNReal.ofReal
        (Real.exp (-(q * ENNReal.toReal
          (twoSidedExitUpTimeCorrected X z ω))))) ω ∂P) := by
        apply lintegral_mono
        intro ω
        by_cases hmem : ω ∈ A
        · have hup := hA hmem
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
