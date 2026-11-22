-- Prove2me | solution 1 for AvramDividend.Classical.avram_jp23_topcap_original_fullnegative_H_nonpositive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T23:11:53.993326+00:00
-- url     : https://prove2.me/submissions/a81ab5c9-36b0-4f14-a512-dd8018fb5c31

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger29_topcap_secant_without_contdiff
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
    ∀ p : ((ℝ≥0 × Ω) × ℝ), H p ≤ 0 := by
  classical
  intro Y H p
  have hGrad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y := by
    intro y hy
    apply hw_grad y hy
    rw [hTop]
    exact ENNReal.ofReal_lt_top
  have hWnonneg : ∀ y : ℝ, 0 ≤ y → 0 ≤ w y := by
    intro y hy
    have hSec :=
      avram_gledger29_topcap_secant_without_contdiff
        w hw_cont hGrad 0 y le_rfl hy
    linarith only [hSec, hw0, hy]
  dsimp only [H]
  split_ifs with h
  · rcases h with ⟨_, _, _, hy, _, hz⟩
    have hDiff : w (Y p.1 + p.2) - w (Y p.1) ≤ 0 := by
      by_cases hIn : 0 ≤ Y p.1 + p.2
      · have hOrder : Y p.1 + p.2 ≤ Y p.1 := by
          linarith only [hz]
        have hSec :=
          avram_gledger29_topcap_secant_without_contdiff
            w hw_cont hGrad (Y p.1 + p.2) (Y p.1) hIn hOrder
        linarith only [hSec, hz]
      · have hNeg : Y p.1 + p.2 < 0 := lt_of_not_ge hIn
        rw [hw_neg _ hNeg]
        have hW := hWnonneg (Y p.1) hy
        linarith only [hW]
    exact mul_nonpos_of_nonneg_of_nonpos (Real.exp_pos _).le hDiff
  · exact le_rfl
