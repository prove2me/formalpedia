-- Prove2me | solution 1 for AvramDividend.Classical.avram_jp23_topcap_fullnegative_H_absolute_source_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:25:07.951849+00:00
-- url     : https://prove2.me/submissions/6c7edda5-f3ea-4946-9791-dd286ac22148

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger29_topcap_secant_without_contdiff
import Theorems.Thm_AvramDividend_Classical_avram_jp23_topcap_original_fullnegative_H_nonpositive
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hTop : C = ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (q : ℝ) (σ : Ω → ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p =>
      Function.leftLim
        (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if 0 < p.1.1 ∧ p.1.1 ≤ σ p.1.2 ∧
          (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 ∧
          0 ≤ Y p.1 ∧ ENNReal.ofReal (Y p.1) ≤ C ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Y p.1 + p.2) - w (Y p.1))
      else 0
    ∀ p : ((ℝ≥0 × Ω) × ℝ),
      ‖H p‖ ≤ Real.exp (-(q * (p.1.1 : ℝ))) * w (Y p.1) := by
  classical
  intro Y H p
  have hGrad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y := by
    intro y hy
    apply hw_grad y hy
    rw [hTop]
    exact ENNReal.ofReal_lt_top
  have hW : ∀ y : ℝ, 0 ≤ w y := by
    intro y
    by_cases hy : 0 ≤ y
    · have hSec :=
        avram_gledger29_topcap_secant_without_contdiff
          w hw_cont hGrad 0 y le_rfl hy
      linarith only [hSec, hw0, hy]
    · have hNeg : y < 0 := lt_of_not_ge hy
      rw [hw_neg y hNeg]
  have hSign : H p ≤ 0 :=
    avram_jp23_topcap_original_fullnegative_H_nonpositive
      X x D w C hTop hw0 hw_cont hw_neg hw_grad q σ p
  have hLo :
      -(Real.exp (-(q * (p.1.1 : ℝ))) * w (Y p.1)) ≤ H p := by
    dsimp only [H]
    split_ifs with h
    · have hAfter : 0 ≤ Real.exp (-(q * (p.1.1 : ℝ))) *
          w (Y p.1 + p.2) :=
        mul_nonneg (Real.exp_pos _).le (hW _)
      calc
        -(Real.exp (-(q * (p.1.1 : ℝ))) * w (Y p.1)) ≤
            Real.exp (-(q * (p.1.1 : ℝ))) * w (Y p.1 + p.2) -
            Real.exp (-(q * (p.1.1 : ℝ))) * w (Y p.1) := by
              linarith only [hAfter]
        _ = _ := by ring
    · have hBefore : 0 ≤ Real.exp (-(q * (p.1.1 : ℝ))) *
          w (Y p.1) := mul_nonneg (Real.exp_pos _).le (hW _)
      linarith only [hBefore]
  rw [Real.norm_eq_abs, abs_of_nonpos hSign]
  linarith only [hLo]
