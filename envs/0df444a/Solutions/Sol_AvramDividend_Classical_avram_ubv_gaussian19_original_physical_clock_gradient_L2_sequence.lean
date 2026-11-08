-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian19_original_physical_clock_gradient_L2_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T22:10:28.696713+00:00
-- url     : https://prove2.me/submissions/97a6f0ed-af5e-4da2-ab8c-aa78d3db471c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_trimmed_physical_clock_exists
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian18_original_gradient_elementary_L2_sequence

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter TopologicalSpace AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] (𝓕 : Filtration ℝ≥0 mΩ)
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (T : ℝ≥0) :
    ∃ (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable)),
      ∃ (hfinite : μ Set.univ < ⊤),
      (∀ A : Set (ℝ≥0 × Ω), MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A) ∧
      (letI : IsFiniteMeasure μ := ⟨hfinite⟩
       let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
         (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
       let G : ℝ≥0 × Ω → ℝ := fun p =>
         X.σ * (if Y p ∈ Icc u v then deriv w (Y p) else 0)
       let Tset : Set (Set (ℝ≥0 × Ω)) :=
         {A | (∃ B : Set Ω, MeasurableSet[𝓕.rightCont 0] B ∧
                    A = ({0} ×ˢ B)) ∨
              (∃ t : ℝ≥0, ∃ B : Set Ω, MeasurableSet[𝓕.rightCont t] B ∧
                    A = (Ioi t ×ˢ B))}
       let S : Set (Lp ℝ (2 : ℝ≥0∞) μ) :=
         {z | ∃ (A : Set (ℝ≥0 × Ω))
             (hA : A ∈ insert univ (insert ∅ Tset))
             (hm : MeasurableSet[𝓕.rightCont.predictable] A)
             (hfin : μ A ≠ ⊤),
             indicatorConstLp (2 : ℝ≥0∞) hm hfin (1 : ℝ) = z}
       ∃ e : ℕ → Lp ℝ (2 : ℝ≥0∞) μ,
         (∀ n, e n ∈ Submodule.span ℝ S) ∧
         Tendsto e atTop (𝓝 ((avram_ubv_gaussian17_original_masked_gradient_MemLp
           X x D hD w a b u v hw hau huv hvb μ hfinite).toLp G))) := by
  classical
  obtain ⟨μ, hfinite, hphysical⟩ :=
    avram_p3_b_bvjump_original_predictable_trimmed_physical_clock_exists
      (P := P) 𝓕 T
  refine ⟨μ, hfinite, hphysical, ?_⟩
  letI : IsFiniteMeasure μ := ⟨hfinite⟩
  exact avram_ubv_gaussian18_original_gradient_elementary_L2_sequence
    X x D hD w a b u v hw hau huv hvb μ hfinite
