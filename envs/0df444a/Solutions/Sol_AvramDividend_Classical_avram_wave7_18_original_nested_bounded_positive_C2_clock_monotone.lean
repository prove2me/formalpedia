-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_nested_bounded_positive_C2_clock_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T09:06:35.212197+00:00
-- url     : https://prove2.me/submissions/087b483a-d958-4b66-a3d4-dc35ea05d096

import Mathlib
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2

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
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0)
    (lower₁ upper₁ lower₂ upper₂ : ℝ)
    (hlower₁ : 0 < lower₁) (hlower₂ : 0 < lower₂)
    (hlo : lower₂ ≤ lower₁) (hup : upper₁ ≤ upper₂)
    (hcap₁ : ∀ y ∈ Set.Icc lower₁ upper₁, ENNReal.ofReal y < C)
    (hcap₂ : ∀ y ∈ Set.Icc lower₂ upper₂, ENNReal.ofReal y < C)
    (hdense : DenseRange r)
    (B₁ B₂ : ℝ≥0) (hB : B₁ ≤ B₂) :
    let τ₁ : Ω → WithTop ℝ≥0 := fun ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower₁ ∨
            upper₁ < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B₁ : WithTop ℝ≥0)
    let τ₂ : Ω → WithTop ℝ≥0 := fun ω =>
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower₂ ∨
            upper₂ < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B₂ : WithTop ℝ≥0)
    IsStoppingTime 𝓕.rightCont τ₁ ∧
      IsStoppingTime 𝓕.rightCont τ₂ ∧
      ∀ ω, τ₁ ω ≤ τ₂ ω := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · exact (avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
      X x D hD C w hw r lower₁ upper₁ hlower₁ hcap₁ hdense B₁).1
  · exact (avram_wave7_18_original_dense_bounded_clock_right_left_uniform_C2
      X x D hD C w hw r lower₂ upper₂ hlower₂ hcap₂ hdense B₂).1
  · intro ω
    have hpoint (k : ℕ) :
        (if x + X.X (r k) ω - rightLimit D (r k) ω < lower₁ ∨
              upper₁ < x + X.X (r k) ω - rightLimit D (r k) ω
         then (r k : WithTop ℝ≥0) else ⊤) ≤
        (if x + X.X (r k) ω - rightLimit D (r k) ω < lower₂ ∨
              upper₂ < x + X.X (r k) ω - rightLimit D (r k) ω
         then (r k : WithTop ℝ≥0) else ⊤) := by
      by_cases hwide :
          x + X.X (r k) ω - rightLimit D (r k) ω < lower₂ ∨
            upper₂ < x + X.X (r k) ω - rightLimit D (r k) ω
      · have hnarrow :
            x + X.X (r k) ω - rightLimit D (r k) ω < lower₁ ∨
              upper₁ < x + X.X (r k) ω - rightLimit D (r k) ω := by
          rcases hwide with hl | hu
          · exact Or.inl (lt_of_lt_of_le hl hlo)
          · exact Or.inr (lt_of_le_of_lt hup hu)
        simpa only [if_pos hnarrow, if_pos hwide] using
          (le_refl (r k : WithTop ℝ≥0))
      · by_cases hnarrow :
            x + X.X (r k) ω - rightLimit D (r k) ω < lower₁ ∨
              upper₁ < x + X.X (r k) ω - rightLimit D (r k) ω
        · simpa only [if_pos hnarrow, if_neg hwide] using
            (le_top : (r k : WithTop ℝ≥0) ≤ ⊤)
        · simpa only [if_neg hnarrow, if_neg hwide] using
            (le_refl (⊤ : WithTop ℝ≥0))
    have hInf :
        (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower₁ ∨
              upper₁ < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) ≤
        (⨅ k : ℕ,
          if x + X.X (r k) ω - rightLimit D (r k) ω < lower₂ ∨
              upper₂ < x + X.X (r k) ω - rightLimit D (r k) ω
          then (r k : WithTop ℝ≥0) else ⊤) :=
      iInf_mono hpoint
    exact min_le_min hInf (WithTop.coe_le_coe.mpr hB)
