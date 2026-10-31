-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_03_dividendMeasure_Icc_zero_eq_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T07:26:51.870986+00:00
-- url     : https://prove2.me/submissions/05700ad1-f61f-48e9-a5c1-e10dad8349b4

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) :
    dividendMeasure D ω (Icc (0 : ℝ) (T : ℝ)) =
      ENNReal.ofReal (rightLimit D T ω) := by
  have hDnonneg : 0 ≤ D T ω := by
    have hm := hD.2.1 ω (show (0 : ℝ≥0) ≤ T from zero_le)
    simpa only [hD.1 ω] using hm
  have hright : D T ω ≤ rightLimit D T ω := by
    unfold rightLimit
    apply le_ciInf
    intro s
    exact hD.2.1 ω (le_of_lt s.property)
  have hnonnegJump : 0 ≤ rightLimit D T ω - D T ω :=
    sub_nonneg.mpr hright
  have hset :
      Icc (0 : ℝ) (T : ℝ) = Ico (0 : ℝ) (T : ℝ) ∪ {(T : ℝ)} := by
    ext t
    simp only [mem_Icc, mem_union, mem_Ico, mem_singleton_iff]
    constructor
    · rintro ⟨h0, ht⟩
      rcases lt_or_eq_of_le ht with hlt | heq
      · exact Or.inl ⟨h0, hlt⟩
      · exact Or.inr heq
    · rintro (⟨h0, ht⟩ | heq)
      · exact ⟨h0, ht.le⟩
      · subst t
        exact ⟨by exact_mod_cast (show (0 : ℝ≥0) ≤ T from zero_le), le_rfl⟩
  have hdisjoint :
      Disjoint (Ico (0 : ℝ) (T : ℝ)) ({(T : ℝ)} : Set ℝ) := by
    refine disjoint_left.mpr ?_
    intro t ht htT
    have heq : t = (T : ℝ) := by simpa using htT
    have hlt : t < (T : ℝ) := ht.2
    simp [heq] at hlt
  calc
    dividendMeasure D ω (Icc (0 : ℝ) (T : ℝ)) =
      dividendMeasure D ω (Ico (0 : ℝ) (T : ℝ)) +
        dividendMeasure D ω {(T : ℝ)} := by
      rw [hset]
      exact measure_union hdisjoint (measurableSet_singleton (T : ℝ))
    _ = ENNReal.ofReal (D T ω) +
        ENNReal.ofReal (rightLimit D T ω - D T ω) := by
      rw [dividendMeasure_Ico_zero_eq_dividendValue D hD ω T,
        dividendMeasure_singleton_eq_rightLimit_sub D hD ω T]
    _ = ENNReal.ofReal (rightLimit D T ω) := by
      rw [← ENNReal.ofReal_add hDnonneg hnonnegJump]
      congr 1
      ring
