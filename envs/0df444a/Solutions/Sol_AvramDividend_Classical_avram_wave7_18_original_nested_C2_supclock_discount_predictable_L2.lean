-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_18_original_nested_C2_supclock_discount_predictable_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T12:58:23.13092+00:00
-- url     : https://prove2.me/submissions/378fca75-24e8-45c4-b576-9caeda46a33a

import Mathlib
import Mathlib.Probability.Process.Predictable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_18_original_nested_C2_supremum_clock_is_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal Classical
open AvramDividend.Classical
noncomputable section

/-- The original nested right-continuous stopped discount has finite quadratic energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (r : ℕ → ℝ≥0) (hdense : DenseRange r)
    (lower upper : ℕ → ℝ) (B : ℕ → ℝ≥0)
    (hlower : ∀ n, 0 < lower n)
    (hlo : ∀ n, lower (n + 1) ≤ lower n)
    (hup : ∀ n, upper n ≤ upper (n + 1))
    (hcap : ∀ n, ∀ y ∈ Set.Icc (lower n) (upper n), ENNReal.ofReal y < C)
    (hB : ∀ n, B n ≤ B (n + 1))
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let τ : Ω → WithTop ℝ≥0 := fun ω => ⨆ n : ℕ,
      min (⨅ k : ℕ,
        if x + X.X (r k) ω - rightLimit D (r k) ω < lower n ∨
            upper n < x + X.X (r k) ω - rightLimit D (r k) ω
        then (r k : WithTop ℝ≥0) else ⊤) (B n : WithTop ℝ≥0)
    let a : ℝ≥0 × Ω → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
        (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    Measurable[𝓕.rightCont.predictable] a ∧
      (∀ p, |a p| ≤ (1 : ℝ)) ∧
      (∀ p, T < p.1 → a p = 0) ∧
      (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((a p) ^ 2) ∂μ) < ⊤ := by
  intro τ a
  have hStop : IsStoppingTime 𝓕.rightCont τ :=
    avram_wave7_18_original_nested_C2_supremum_clock_is_stopping
      X x D hD C w hw r hdense lower upper B hlower hlo hup hcap hB
  have hDisc :=
    avram_wave6_04_original_rightcont_randomly_stopped_discount_weight_predictable
      τ hStop q hq T
  dsimp only at hDisc
  have hMeas : Measurable[𝓕.rightCont.predictable] a := by
    convert hDisc.1 using 1
    funext p
    by_cases ht : p.1 ≤ T <;>
      by_cases hτ : (p.1 : ℝ≥0∞) ≤ τ p.2 <;>
      simp [a, ht, hτ]
  have hBound : ∀ p, |a p| ≤ (1 : ℝ) := by
    intro p
    convert hDisc.2.1 p using 1 <;>
      (by_cases ht : p.1 ≤ T <;>
       by_cases hτ : (p.1 : ℝ≥0∞) ≤ τ p.2 <;>
       simp [a, ht, hτ])
  have hZero : ∀ p, T < p.1 → a p = 0 := by
    intro p hp
    simp [a, not_le.mpr hp]
  refine ⟨hMeas, hBound, hZero, ?_⟩
  have hSq (p : ℝ≥0 × Ω) : (a p)^2 ≤ (1 : ℝ) := by
    have hb := hBound p
    have hprod : 0 ≤ (1 - |a p|) * (1 + |a p|) :=
      mul_nonneg (sub_nonneg.mpr hb) (by positivity)
    nlinarith [sq_abs (a p)]
  have hpoint (p : ℝ≥0 × Ω) :
      ENNReal.ofReal ((a p)^2) ≤ (1 : ℝ≥0∞) := by
    simpa using ENNReal.ofReal_le_ofReal (hSq p)
  calc
    (∫⁻ p : ℝ≥0 × Ω, ENNReal.ofReal ((a p)^2) ∂μ) ≤
        ∫⁻ _ : ℝ≥0 × Ω, (1 : ℝ≥0∞) ∂μ := lintegral_mono hpoint
    _ = μ Set.univ := by simp
    _ < ⊤ := hμ
