-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_08_original_strict_interior_dividendMeasure_rightLimit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:53:21.877847+00:00
-- url     : https://prove2.me/submissions/c6009b26-d0ed-489c-8b5e-4ab18d0da94b

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_eq_dividend_increment
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
/-- Strictly interior original Stieltjes mass excludes both endpoint right payments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a < b) :
    dividendMeasure D ω (Ioo (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (D b ω - rightLimit D a ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  have habR : (a : ℝ) < (b : ℝ) := by exact_mod_cast hab
  have hsplit : Ico (a : ℝ) (b : ℝ) =
      ({(a : ℝ)} : Set ℝ) ∪ Ioo (a : ℝ) (b : ℝ) := by
    ext t
    simp only [mem_Ico, mem_union, mem_singleton_iff, mem_Ioo]
    constructor
    · rintro ⟨hta, htb⟩
      rcases eq_or_lt_of_le hta with heq | hlt
      · exact Or.inl heq.symm
      · exact Or.inr ⟨hlt, htb⟩
    · rintro (rfl | ⟨hta, htb⟩)
      · exact ⟨le_refl _, habR⟩
      · exact ⟨le_of_lt hta, htb⟩
  have hdisjoint :
      Disjoint ({(a : ℝ)} : Set ℝ) (Ioo (a : ℝ) (b : ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro t ht hIoo
    simp only [mem_singleton_iff] at ht
    subst t
    exact (lt_irrefl (a : ℝ)) hIoo.1
  have hmeas : μ (Ico (a : ℝ) (b : ℝ)) =
      μ ({(a : ℝ)} : Set ℝ) + μ (Ioo (a : ℝ) (b : ℝ)) := by
    rw [hsplit]
    exact measure_union hdisjoint measurableSet_Ioo
  have hinc : D a ω ≤ rightLimit D a ω :=
    dividendStrategy_le_rightLimit D hD ω a
  have hmono : D a ω ≤ D b ω := hD.2.1 ω (le_of_lt hab)
  have hfinAtom : μ ({(a : ℝ)} : Set ℝ) ≠ ⊤ := by
    change dividendMeasure D ω ({(a : ℝ)} : Set ℝ) ≠ ⊤
    rw [dividendMeasure_singleton_eq_rightLimit_sub D hD ω a]
    exact ENNReal.ofReal_ne_top
  have hfinIco : μ (Ico (a : ℝ) (b : ℝ)) ≠ ⊤ := by
    change dividendMeasure D ω (Ico (a : ℝ) (b : ℝ)) ≠ ⊤
    rw [dividendMeasure_Ico_eq_dividend_increment D hD ω a b]
    exact ENNReal.ofReal_ne_top
  have hle : μ (Ioo (a : ℝ) (b : ℝ)) ≤ μ (Ico (a : ℝ) (b : ℝ)) :=
    measure_mono (by
      intro t ht
      exact ⟨le_of_lt ht.1, ht.2⟩)
  have hfinOpen : μ (Ioo (a : ℝ) (b : ℝ)) ≠ ⊤ :=
    ne_top_of_le_ne_top hfinIco hle
  have hsum := congrArg ENNReal.toReal hmeas
  rw [ENNReal.toReal_add hfinAtom hfinOpen] at hsum
  rw [show μ (Ico (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (D b ω - D a ω) from
        dividendMeasure_Ico_eq_dividend_increment D hD ω a b,
      show μ ({(a : ℝ)} : Set ℝ) =
      ENNReal.ofReal (rightLimit D a ω - D a ω) from
        dividendMeasure_singleton_eq_rightLimit_sub D hD ω a,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hmono),
      ENNReal.toReal_ofReal (sub_nonneg.mpr hinc)] at hsum
  have hreal : (μ (Ioo (a : ℝ) (b : ℝ))).toReal =
      D b ω - rightLimit D a ω := by linarith only [hsum]
  change μ (Ioo (a : ℝ) (b : ℝ)) =
      ENNReal.ofReal (D b ω - rightLimit D a ω)
  calc
    μ (Ioo (a : ℝ) (b : ℝ)) =
        ENNReal.ofReal (μ (Ioo (a : ℝ) (b : ℝ))).toReal := by
          exact (ENNReal.ofReal_toReal hfinOpen).symm
    _ = ENNReal.ofReal (D b ω - rightLimit D a ω) := by rw [hreal]
