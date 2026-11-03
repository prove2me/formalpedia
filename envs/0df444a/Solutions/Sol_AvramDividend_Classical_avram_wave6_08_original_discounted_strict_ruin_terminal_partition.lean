-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_discounted_strict_ruin_terminal_partition
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:53:49.375638+00:00
-- url     : https://prove2.me/submissions/6f7745df-678e-4f13-ad0b-77e3c854d208

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact full original Stieltjes grid cell plus strictly pre-ruin final cell,
including the interior right atom and excluding the terminal ruin right atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (a b c : ℝ≥0) (hab : a < b) (hbc : b < c) :
    (∫⁻ t in Ioo (a : ℝ) (c : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in Ioc (a : ℝ) (b : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in Ioo (b : ℝ) (c : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hbcR : (b : ℝ) < (c : ℝ) := by exact_mod_cast hbc
  have hsplit : Ioo (a : ℝ) (c : ℝ) =
      Ioc (a : ℝ) (b : ℝ) ∪ Ioo (b : ℝ) (c : ℝ) := by
    ext t
    simp only [mem_Ioo, mem_union, mem_Ioc]
    constructor
    · rintro ⟨hta, htc⟩
      by_cases htb : t ≤ (b : ℝ)
      · exact Or.inl ⟨hta, htb⟩
      · exact Or.inr ⟨lt_of_not_ge htb, htc⟩
    · rintro (⟨hta, htb⟩ | ⟨htb, htc⟩)
      · exact ⟨hta, lt_of_le_of_lt htb hbcR⟩
      · exact ⟨lt_trans habR htb, htc⟩
  have hdisjoint :
      Disjoint (Ioc (a : ℝ) (b : ℝ)) (Ioo (b : ℝ) (c : ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro t hleft hright
    exact (not_lt_of_ge hleft.2) hright.1
  rw [hsplit]
  exact lintegral_union measurableSet_Ioo hdisjoint
