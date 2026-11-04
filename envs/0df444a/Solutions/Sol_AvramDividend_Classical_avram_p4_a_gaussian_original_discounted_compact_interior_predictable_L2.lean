-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_a_gaussian_original_discounted_compact_interior_predictable_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:09:29.020343+00:00
-- url     : https://prove2.me/submissions/7722524d-1d34-4731-885f-cc4dd7e7eb0e

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_gaussian_localized_gradient_MemLp_two_export

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact source Gaussian coefficient and discounted pre-payment derivative
are predictable L² on any compact interior band and finite predictable clock. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b u v : ℝ) (ha : 0 < a) (hau : a < u) (huv : u ≤ v)
    (hvb : v < b)
    (hband : ∀ y : ℝ, y ∈ Ioo a b → ENNReal.ofReal y < C)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Upre : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Upre p ∈ Icc u v then deriv w (Upre p) else 0
    @MemLp (ℝ≥0 × Ω) ℝ (𝓕.rightCont.predictable) _ _
      (fun p => (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0)
        * (X.σ * G p)) 2 μ := by
  have hC2 : ContDiffOn ℝ 2 w (Ioo a b) :=
    hw.mono (by
      intro y hy
      exact ⟨lt_trans ha hy.1, hband y hy⟩)
  have hweight :=
    avram_wave6_02_original_rightcont_horizon_discount_weight_predictable_bounded
      (𝓕 := 𝓕) q hq T
  dsimp only at hweight
  exact avram_wave5_03a_original_gaussian_localized_gradient_MemLp_two_export
    X x D hD.1.1 w a b u v hC2 hau huv hvb
    (fun p => if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0)
    hweight.1 hweight.2.1 μ hμ
