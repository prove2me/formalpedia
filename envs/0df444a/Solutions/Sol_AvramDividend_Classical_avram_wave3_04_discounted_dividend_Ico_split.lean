-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_04_discounted_dividend_Ico_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-29T23:43:12.717018+00:00
-- url     : https://prove2.me/submissions/66a7bf6f-d736-4561-9ff6-c040764c9dbf

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The entire discounted Stieltjes dividend reward, including diffuse
and right-jump mass, splits exactly at an intermediate time. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (a b c : ℝ≥0)
    (hab : a ≤ b) (hbc : b ≤ c) :
    (∫⁻ s in Ico (a : ℝ) (c : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) =
    (∫⁻ s in Ico (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) +
    (∫⁻ s in Ico (b : ℝ) (c : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) := by
  have hab' : (a : ℝ) ≤ (b : ℝ) := NNReal.coe_mono hab
  have hbc' : (b : ℝ) ≤ (c : ℝ) := NNReal.coe_mono hbc
  have hunion : Ico (a : ℝ) (b : ℝ) ∪
      Ico (b : ℝ) (c : ℝ) = Ico (a : ℝ) (c : ℝ) := by
    ext x
    constructor
    · rintro (⟨hax, hxb⟩ | ⟨hbx, hxc⟩)
      · exact ⟨hax, lt_of_lt_of_le hxb hbc'⟩
      · exact ⟨le_trans hab' hbx, hxc⟩
    · rintro ⟨hax, hxc⟩
      by_cases hxb : x < (b : ℝ)
      · exact Or.inl ⟨hax, hxb⟩
      · exact Or.inr ⟨le_of_not_gt hxb, hxc⟩
  have hdisj : Disjoint (Ico (a : ℝ) (b : ℝ))
      (Ico (b : ℝ) (c : ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro x hx hy
    exact (not_lt_of_ge hy.1) hx.2
  rw [← hunion]
  exact lintegral_union measurableSet_Ico hdisj
