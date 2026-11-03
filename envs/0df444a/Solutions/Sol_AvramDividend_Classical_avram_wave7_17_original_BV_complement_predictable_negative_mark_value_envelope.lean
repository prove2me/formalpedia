-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_17_original_BV_complement_predictable_negative_mark_value_envelope
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:56:25.387256+00:00
-- url     : https://prove2.me/submissions/da39eaf1-0563-4307-ac7e-6abcfbbcf819

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ) (hH : 0 ≤ H)
    (hEnvelope : ¬ (x + H * X.drift ≤ w x))
    (ω : Ω) (t : ℝ≥0) (z : ℝ) (hz : z < 0)
    (hy : 0 < Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t ∧
      ENNReal.ofReal (Function.leftLim (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω) t) < C) :
    let y := Function.leftLim (fun s : ℝ≥0 =>
      x + X.X s ω - rightLimit D s ω) t
    0 < X.drift ∧
      -w y ≤ w (y + z) - w y ∧
      w (y + z) - w y ≤ 0 := by
  dsimp only
  let y : ℝ := Function.leftLim (fun s : ℝ≥0 =>
    x + X.X s ω - rightLimit D s ω) t
  have hy0 : 0 < y := hy.1
  have hyC : ENNReal.ofReal y < C := hy.2
  have hdpos : 0 < X.drift := by
    obtain ⟨_, hd, _, _⟩ :=
      avram_wave7_17_original_BV_strict_complement_sharp_drift_budget
        X hX hBV q hq w C hC hw_cont hw0 hw_smooth hw_grad
        x hx hxc D hD H hH hEnvelope
    exact hd
  have hyC' : ENNReal.ofReal y ≤ C := le_of_lt hyC
  have hSec0 :=
    avram_wave3_03_bv_full_cap_gradient_secant
      C hC w hw_cont hw_smooth hw_grad 0 y
      (le_refl (0 : ℝ)) (le_of_lt hy0) hyC'
  have hwy : 0 ≤ w y := by
    linarith only [hSec0, hw0, hy0]
  refine ⟨hdpos, ?_⟩
  by_cases hneg : y + z < 0
  · have hwneg : w (y + z) = 0 := hw_neg _ hneg
    rw [hwneg]
    constructor <;> linarith
  · have hres0 : 0 ≤ y + z := le_of_not_gt hneg
    have hresle : y + z ≤ y := by linarith
    have hresC : ENNReal.ofReal (y + z) ≤ C :=
      (ENNReal.ofReal_mono hresle).trans hyC'
    have hSecRes :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad 0 (y + z)
        (le_refl (0 : ℝ)) hres0 hresC
    have hwres : 0 ≤ w (y + z) := by linarith
    have hSecStep :=
      avram_wave3_03_bv_full_cap_gradient_secant
        C hC w hw_cont hw_smooth hw_grad (y + z) y
        hres0 hresle hyC'
    constructor <;> linarith
