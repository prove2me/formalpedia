-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_finite_horizon_full_cash_zero_plus_preterminal
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:21:07.212944+00:00
-- url     : https://prove2.me/submissions/2c7d77a0-5867-4c5f-a390-abddc3f72eaa

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
import Theorems.Thm_AvramDividend_Classical_avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- Exact original discounted full Stieltjes cash: the zero atom is retained;
the positive endpoint is included only strictly before positive finite ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (τ : ℝ≥0) (hτ : 0 < τ)
    (T : ℝ) (hT : 0 ≤ T) :
    (∫⁻ t in paymentTimes (τ : ℝ≥0∞) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) =
    (∫⁻ t in ({(0 : ℝ)} : Set ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) +
    (if T < (τ : ℝ) then
      (∫⁻ t in Ioc (0 : ℝ) T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
     else
      (∫⁻ t in Ioo (0 : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by
  by_cases hcase : T < (τ : ℝ)
  · have hsplit : Icc (0 : ℝ) T =
        ({(0 : ℝ)} : Set ℝ) ∪ Ioc (0 : ℝ) T := by
      ext t
      simp only [mem_Icc, mem_union, mem_singleton_iff, mem_Ioc]
      constructor
      · rintro ⟨ht0, htT⟩
        by_cases hz : t = 0
        · exact Or.inl hz
        · exact Or.inr ⟨lt_of_le_of_ne ht0 (Ne.symm hz), htT⟩
      · rintro (rfl | ⟨ht0, htT⟩)
        · exact ⟨le_refl _, hT⟩
        · exact ⟨le_of_lt ht0, htT⟩
    have hdisjoint :
        Disjoint ({(0 : ℝ)} : Set ℝ) (Ioc (0 : ℝ) T) := by
      refine Set.disjoint_left.mpr ?_
      intro t ht hIoc
      simp only [mem_singleton_iff] at ht
      subst t
      exact (lt_irrefl (0 : ℝ)) hIoc.1
    rw [avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
      τ hτ T hT]
    simp only [if_pos hcase]
    rw [hsplit]
    exact lintegral_union measurableSet_Ioc hdisjoint
  · have hsame :
        paymentTimes (τ : ℝ≥0∞) ∩ Iic T =
          paymentTimes (τ : ℝ≥0∞) ∩ Iic (τ : ℝ) := by
      rw [avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
        τ hτ T hT,
        avram_wave6_08_original_positive_ruin_real_horizon_payment_clip_exact
        τ hτ (τ : ℝ) (le_of_lt (by exact_mod_cast hτ))]
      simp [hcase]
    rw [hsame]
    simpa only [if_neg hcase] using
      (avram_wave6_08_original_positive_finite_ruin_full_cash_zero_atom_plus_strict_left
        D hD ω q τ hτ)
