-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_l2_dense_adapted_boolean_indicator_span
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T18:12:30.931387+00:00
-- url     : https://prove2.me/submissions/4826604c-ad91-4fef-a1f8-a9905bf06d13

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_generator_set_algebra_measure_dense

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set TopologicalSpace AvramDividend.Classical
open scoped ENNReal NNReal

/-- Every L² predictable time-history function on the original filtration
lies in the L² closure of the real linear span of indicators of finite
Boolean combinations of genuinely adapted past rectangles. -/
theorem solution
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι]
    (𝓕 : Filtration ι mΩ)
    [mProd : MeasurableSpace (ι × Ω)]
    (hProd : mProd = 𝓕.predictable)
    (μ : Measure (ι × Ω)) [IsFiniteMeasure μ] :
    let G : Set (Set (ι × Ω)) :=
      {T | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                T = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                T = (Set.Ioi i ×ˢ A))}
    let hG : μ.MeasureDense (generateSetAlgebra G) :=
      avram_wave4_p1_predictable_generator_set_algebra_measure_dense 𝓕 hProd μ
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set (ι × Ω)) (ht : t ∈ generateSetAlgebra G)
        (hμt : μ t ≠ ⊤) (c : ℝ),
        indicatorConstLp (2 : ℝ≥0∞) (hG.measurable t ht) hμt c = v}
    ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
      f ∈ (Submodule.span ℝ S).topologicalClosure := by
  classical
  letI : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  letI : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩
  let G : Set (Set (ι × Ω)) :=
    {T | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
              T = ({⊥} ×ˢ A)) ∨
         (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
              T = (Set.Ioi i ×ˢ A))}
  let hG : μ.MeasureDense (generateSetAlgebra G) :=
    avram_wave4_p1_predictable_generator_set_algebra_measure_dense 𝓕 hProd μ
  let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
    {v | ∃ (t : Set (ι × Ω)) (ht : t ∈ generateSetAlgebra G)
      (hμt : μ t ≠ ⊤) (c : ℝ),
      indicatorConstLp (2 : ℝ≥0∞) (hG.measurable t ht) hμt c = v}
  change ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
    f ∈ (Submodule.span ℝ S).topologicalClosure
  let M : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) μ) :=
    (Submodule.span ℝ S).topologicalClosure
  have hFixed (c : ℝ) :
      {indicatorConstLp (2 : ℝ≥0∞) (hG.measurable t ht) hμt c |
        (t : Set (ι × Ω)) (ht : t ∈ generateSetAlgebra G) (hμt : μ t ≠ ⊤)}
      ⊆ S := by
    rintro v ⟨t, ht, hμt, rfl⟩
    exact ⟨t, ht, hμt, c, rfl⟩
  have hIndicator (c : ℝ) {t : Set (ι × Ω)}
      (ht : MeasurableSet t) (hμt : μ t ≠ ⊤) :
      indicatorConstLp (2 : ℝ≥0∞) ht hμt c ∈ M := by
    have hApprox :
        indicatorConstLp (2 : ℝ≥0∞) ht hμt c ∈
          closure {indicatorConstLp (2 : ℝ≥0∞) (hG.measurable u hu) hμu c |
            (u : Set (ι × Ω)) (hu : u ∈ generateSetAlgebra G) (hμu : μ u ≠ ⊤)} :=
      hG.indicatorConstLp_subset_closure (2 : ℝ≥0∞) c
        ⟨t, ht, hμt, rfl⟩
    exact (Submodule.closure_subset_topologicalClosure_span (R := ℝ) S)
      ((closure_mono (hFixed c)) hApprox)
  have hAll : ∀ f : Lp ℝ (2 : ℝ≥0∞) μ, f ∈ M := by
    apply Lp.induction (p := (2 : ℝ≥0∞)) (by norm_num)
      (motive := fun f => f ∈ M)
    · intro c t ht hμt
      simpa only [Lp.simpleFunc.coe_indicatorConst] using
        hIndicator c ht hμt.ne
    · intro f g hf hg hdisj hfm hgm
      exact M.add_mem hfm hgm
    · exact Submodule.isClosed_topologicalClosure _
  exact hAll