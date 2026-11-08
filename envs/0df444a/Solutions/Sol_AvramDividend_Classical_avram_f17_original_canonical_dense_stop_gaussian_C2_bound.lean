-- Prove2me | solution 1 for AvramDividend.Classical.avram_f17_original_canonical_dense_stop_gaussian_C2_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T09:04:11.442753+00:00
-- url     : https://prove2.me/submissions/746e8278-7e3a-4142-bcd8-560c9c566d74

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_f17_original_dense_bounded_stop_exact_gaussian_C2_bound
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (q : ℝ) (hq : 0 ≤ q) (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (lower upper : ℝ) (hlower : 0 < lower)
    (hcap : ∀ y ∈ Set.Icc lower upper, ENNReal.ofReal y < C)
    (B : ℝ≥0) :
    IsStoppingTime 𝓕.rightCont (fun ω : Ω =>
      min (⨅ k : ℕ,
        if x + X.X ((TopologicalSpace.denseSeq ℝ≥0) k) ω -
            rightLimit D ((TopologicalSpace.denseSeq ℝ≥0) k) ω < lower ∨
              upper < x + X.X ((TopologicalSpace.denseSeq ℝ≥0) k) ω -
                rightLimit D ((TopologicalSpace.denseSeq ℝ≥0) k) ω
        then ((TopologicalSpace.denseSeq ℝ≥0) k : WithTop ℝ≥0) else ⊤)
        (B : WithTop ℝ≥0)) ∧
    ∃ KG KH : ℝ, 0 ≤ KG ∧ 0 ≤ KH ∧
      ∀ (ω : Ω) (T : ℝ≥0),
        (T : WithTop ℝ≥0) ≤ min (⨅ k : ℕ,
          if x + X.X ((TopologicalSpace.denseSeq ℝ≥0) k) ω -
              rightLimit D ((TopologicalSpace.denseSeq ℝ≥0) k) ω < lower ∨
                upper < x + X.X ((TopologicalSpace.denseSeq ℝ≥0) k) ω -
                  rightLimit D ((TopologicalSpace.denseSeq ℝ≥0) k) ω
          then ((TopologicalSpace.denseSeq ℝ≥0) k : WithTop ℝ≥0) else ⊤)
          (B : WithTop ℝ≥0) →
        ∀ t : ℝ≥0, 0 < t → t < T →
          let y := Function.leftLim
            (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
          y ∈ Set.Icc lower upper ∧
            |Real.exp (-(q * (t : ℝ))) * deriv w y| ≤ KG ∧
            |Real.exp (-(q * (t : ℝ))) * iteratedDeriv 2 w y| ≤ KH := by
  have hdense : DenseRange (TopologicalSpace.denseSeq ℝ≥0) :=
    TopologicalSpace.denseRange_denseSeq ℝ≥0
  exact avram_f17_original_dense_bounded_stop_exact_gaussian_C2_bound
    X hBV hν q hq C w hw x D hD (TopologicalSpace.denseSeq ℝ≥0)
    lower upper hlower hcap hdense B
