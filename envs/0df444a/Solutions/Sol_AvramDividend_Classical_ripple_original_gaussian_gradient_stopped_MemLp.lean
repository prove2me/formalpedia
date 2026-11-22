-- Prove2me | solution 1 for AvramDividend.Classical.ripple_original_gaussian_gradient_stopped_MemLp
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:17:21.157833+00:00
-- url     : https://prove2.me/submissions/873c27dd-2b42-4bd7-b2ed-5c42f9342647

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian17_original_masked_gradient_MemLp
import Theorems.Thm_AvramDividend_Classical_ripple_stopping_region_predictable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal
noncomputable section
/-- True original Lévy prepayment Gaussian gradient, stopped at τ.
    Ripple (Apache-2.0) stopped-predictable-region proof, commit
    e216e28ce3ffb43877e11f71be260e40a37a35df. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0))) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    MemLp ({p : ℝ≥0 × Ω | 0 < p.1 ∧ (p.1 : WithTop ℝ≥0) ≤ τ p.2}.indicator G) 2 μ  := by
  exact (avram_ubv_gaussian17_original_masked_gradient_MemLp
    X x D hD w a b u v hw hau huv hvb μ hμ).indicator
    (ripple_stopping_region_predictable 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)) hτstop)
