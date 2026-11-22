-- Prove2me | solution 1 for AvramDividend.Classical.avram_ftap_dividendMeasure_stopped_Ioc_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-22T11:14:50.942631+00:00
-- url     : https://prove2.me/submissions/d60ce082-d405-4411-9f2e-e85943f279f3

/-
Copyright (c) 2026 Mocho Go. All rights reserved.
Adapted proof structure from FTAPTheorem42/Stochastic/FiniteVariation/FiniteVariationStoppedStieltjes.lean
Upstream commit 8c9c46e1b6e455f7d3069062957d4363879836ce
Released under Apache-2.0.
-/
import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ a b : ℝ≥0) (hab : a ≤ b) :
    ((dividendMeasure D ω).restrict (Ioc (0 : ℝ) (τ : ℝ)))
      (Ioc (a : ℝ) (b : ℝ)) =
        ENNReal.ofReal (rightLimit D (min b τ) ω -
          rightLimit D (min a τ) ω) := by
  rw [Measure.restrict_apply measurableSet_Ioc]
  by_cases hτa : τ ≤ a
  · have hInter : Ioc (a : ℝ) (b : ℝ) ∩ Ioc (0 : ℝ) (τ : ℝ) = ∅ := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_empty_iff_false, iff_false]
      intro ht
      have hca : (τ : ℝ) ≤ (a : ℝ) := by exact_mod_cast hτa
      exact (not_lt_of_ge hca) (ht.1.1.trans_le ht.2.2)
    rw [hInter]
    simp [min_eq_right hτa, min_eq_right (hτa.trans hab)]
  · have haτ : a ≤ τ := le_of_lt (lt_of_not_ge hτa)
    have hInter :
        Ioc (a : ℝ) (b : ℝ) ∩ Ioc (0 : ℝ) (τ : ℝ) =
          Ioc (a : ℝ) ((min b τ : ℝ≥0) : ℝ) := by
      ext t
      simp only [Set.mem_inter_iff, Set.mem_Ioc, NNReal.coe_min, le_min_iff]
      constructor
      · rintro ⟨⟨hat, htb⟩, ⟨_, htτ⟩⟩
        exact ⟨hat, htb, htτ⟩
      · rintro ⟨hat, htb, htτ⟩
        exact ⟨⟨hat, htb⟩, ⟨lt_of_le_of_lt (by positivity) hat, htτ⟩⟩
    rw [hInter, dividendMeasure_Ioc_rightLimit D hD ω a (min b τ)]
    simp only [min_eq_left haτ]
