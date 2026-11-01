-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_p1_predictable_marked_l2_dense_adapted_boolean_indicator_span
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T18:23:57.566968+00:00
-- url     : https://prove2.me/submissions/bb6accb6-da56-4913-887c-0acff8bfd574

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_predictable_marked_rectangle_algebra_measure_dense

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory MeasurableSpace Set TopologicalSpace AvramDividend.Classical
open scoped ENNReal NNReal

/-- Every scalar square-integrable *marked* predictable kernel for the
original filtration on a finite expected time-history × mark measure lies in
the L² closure of finite adapted Boolean-rectangle indicator sums. -/
theorem solution
    {Ω ι E : Type*} [mΩ : MeasurableSpace Ω]
    [LinearOrder ι] [OrderBot ι] [mE : MeasurableSpace E]
    (𝓕 : Filtration ι mΩ)
    [mHist : MeasurableSpace (ι × Ω)]
    (hHist : mHist = 𝓕.predictable)
    [mMarked : MeasurableSpace ((ι × Ω) × E)]
    (hMarked : mMarked = @Prod.instMeasurableSpace (ι × Ω) E mHist mE)
    (μ : Measure ((ι × Ω) × E)) [IsFiniteMeasure μ] :
    let G : Set (Set (ι × Ω)) :=
      {T | (∃ A : Set Ω, MeasurableSet[𝓕 ⊥] A ∧
                T = ({⊥} ×ˢ A)) ∨
           (∃ i : ι, ∃ A : Set Ω, MeasurableSet[𝓕 i] A ∧
                T = (Set.Ioi i ×ˢ A))}
    let GM : Set (Set ((ι × Ω) × E)) :=
      Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
    let hGM : μ.MeasureDense (generateSetAlgebra GM) :=
      avram_wave4_p1_predictable_marked_rectangle_algebra_measure_dense
        𝓕 hHist hMarked μ
    let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
      {v | ∃ (t : Set ((ι × Ω) × E)) (ht : t ∈ generateSetAlgebra GM)
        (hμt : μ t ≠ ⊤) (c : ℝ),
        indicatorConstLp (2 : ℝ≥0∞) (hGM.measurable t ht) hμt c = v}
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
  let GM : Set (Set ((ι × Ω) × E)) :=
    Set.image2 (· ×ˢ ·) G {C : Set E | MeasurableSet C}
  let hGM : μ.MeasureDense (generateSetAlgebra GM) :=
    avram_wave4_p1_predictable_marked_rectangle_algebra_measure_dense
      𝓕 hHist hMarked μ
  let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
    {v | ∃ (t : Set ((ι × Ω) × E)) (ht : t ∈ generateSetAlgebra GM)
      (hμt : μ t ≠ ⊤) (c : ℝ),
      indicatorConstLp (2 : ℝ≥0∞) (hGM.measurable t ht) hμt c = v}
  change ∀ f : Lp ℝ (2 : ℝ≥0∞) μ,
    f ∈ (Submodule.span ℝ S).topologicalClosure
  let M : Submodule ℝ (Lp ℝ (2 : ℝ≥0∞) μ) :=
    (Submodule.span ℝ S).topologicalClosure
  have hFixed (c : ℝ) :
      {indicatorConstLp (2 : ℝ≥0∞) (hGM.measurable t ht) hμt c |
        (t : Set ((ι × Ω) × E)) (ht : t ∈ generateSetAlgebra GM) (hμt : μ t ≠ ⊤)}
      ⊆ S := by
    rintro v ⟨t, ht, hμt, rfl⟩
    exact ⟨t, ht, hμt, c, rfl⟩
  have hIndicator (c : ℝ) {t : Set ((ι × Ω) × E)}
      (ht : MeasurableSet t) (hμt : μ t ≠ ⊤) :
      indicatorConstLp (2 : ℝ≥0∞) ht hμt c ∈ M := by
    have hApprox :
        indicatorConstLp (2 : ℝ≥0∞) ht hμt c ∈
          closure {indicatorConstLp (2 : ℝ≥0∞) (hGM.measurable u hu) hμu c |
            (u : Set ((ι × Ω) × E)) (hu : u ∈ generateSetAlgebra GM) (hμu : μ u ≠ ⊤)} :=
      hGM.indicatorConstLp_subset_closure (2 : ℝ≥0∞) c
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