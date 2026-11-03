-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:07:18.290604+00:00
-- url     : https://prove2.me/submissions/c380fe3d-59ce-4704-aaeb-039bdff57f69

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Full original stopped dividend cash at positive finite ruin counts the
initial right payment and every strict-left payment, never the ruin right atom. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (τ : ℝ≥0) (hτ : 0 < τ) :
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
      (∫⁻ t in ({(0 : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
      (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) := by
  have hτE : (0 : ℝ≥0∞) < (τ : ℝ≥0∞) := by exact_mod_cast hτ
  have hτR : (0 : ℝ) < (τ : ℝ) := by exact_mod_cast hτ
  have hset : paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ) =
      ({(0 : ℝ)} : Set ℝ) ∪ Ioo (0 : ℝ) (τ : ℝ) := by
    rw [paymentTimes_eq_strict_of_pos (τ : ℝ≥0∞) hτE]
    ext t
    simp only [mem_inter_iff, mem_setOf_eq, mem_Iic,
      mem_union, mem_singleton_iff, mem_Ioo]
    constructor
    · rintro ⟨⟨ht0, htE⟩, _⟩
      by_cases ht : t = 0
      · exact Or.inl ht
      · exact Or.inr ⟨lt_of_le_of_ne ht0 (Ne.symm ht),
          (ENNReal.ofReal_lt_coe_iff ht0).mp htE⟩
    · rintro (ht | ⟨ht0, htτ⟩)
      · subst t
        refine ⟨⟨le_refl _, ?_⟩, le_of_lt hτR⟩
        simpa using hτE
      · exact ⟨⟨le_of_lt ht0,
          (ENNReal.ofReal_lt_coe_iff (le_of_lt ht0)).mpr htτ⟩,
          le_of_lt htτ⟩
  have hdisjoint :
      Disjoint ({(0 : ℝ)} : Set ℝ) (Ioo (0 : ℝ) (τ : ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro t ht hIoo
    simp only [mem_singleton_iff] at ht
    subst t
    exact (lt_irrefl (0 : ℝ)) hIoo.1
  rw [hset]
  exact lintegral_union measurableSet_Ioo hdisjoint
