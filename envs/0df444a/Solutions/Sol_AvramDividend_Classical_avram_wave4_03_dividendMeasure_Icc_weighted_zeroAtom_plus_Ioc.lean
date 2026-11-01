-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_03_dividendMeasure_Icc_weighted_zeroAtom_plus_Ioc
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:26:30.072207+00:00
-- url     : https://prove2.me/submissions/1064d71f-80c7-4ec7-8068-7ea43283247d

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

/-- The true full random Stieltjes integral on [0,T] is its initial right
atom plus the complete (0,T] Stieltjes integral for any ENNReal weight. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ), f s ∂dividendMeasure D ω) =
    ENNReal.ofReal (rightLimit D 0 ω) * f 0 +
      (∫⁻ s in Ioc (0 : ℝ) (T : ℝ), f s ∂dividendMeasure D ω) := by
  let μ : Measure ℝ := dividendMeasure D ω
  have hT : (0 : ℝ) ≤ (T : ℝ) := NNReal.coe_nonneg T
  have hunion :
      ({(0 : ℝ)} : Set ℝ) ∪ Ioc (0 : ℝ) (T : ℝ) =
        Icc (0 : ℝ) (T : ℝ) := by
    ext s
    constructor
    · rintro (hs | hs)
      · have heq : s = 0 := by simpa using hs
        subst s
        exact ⟨le_refl _, hT⟩
      · exact ⟨le_of_lt hs.1, hs.2⟩
    · intro hs
      rcases lt_or_eq_of_le hs.1 with hp | hz
      · exact Or.inr ⟨hp, hs.2⟩
      · exact Or.inl (by simpa using hz.symm)
  have hdisj : Disjoint ({(0 : ℝ)} : Set ℝ)
      (Ioc (0 : ℝ) (T : ℝ)) := by
    refine Set.disjoint_left.mpr ?_
    intro s hs ht
    have heq : s = 0 := by simpa using hs
    subst s
    exact (not_lt_of_ge (le_refl (0 : ℝ))) ht.1
  have hAtom : μ {(0 : ℝ)} = ENNReal.ofReal (rightLimit D 0 ω) := by
    simpa [μ, hD.1 ω] using
      (dividendMeasure_singleton_eq_rightLimit_sub D hD ω (0 : ℝ≥0))
  calc
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ), f s ∂dividendMeasure D ω) =
        (∫⁻ s in ({(0 : ℝ)} : Set ℝ) ∪ Ioc (0 : ℝ) (T : ℝ),
          f s ∂μ) := by rw [hunion]
    _ = (∫⁻ s in ({(0 : ℝ)} : Set ℝ), f s ∂μ) +
        (∫⁻ s in Ioc (0 : ℝ) (T : ℝ), f s ∂μ) :=
      lintegral_union measurableSet_Ioc hdisj
    _ = ENNReal.ofReal (rightLimit D 0 ω) * f 0 +
        (∫⁻ s in Ioc (0 : ℝ) (T : ℝ), f s ∂dividendMeasure D ω) := by
      rw [lintegral_singleton, hAtom]
      simp only [μ]
      ac_rfl
