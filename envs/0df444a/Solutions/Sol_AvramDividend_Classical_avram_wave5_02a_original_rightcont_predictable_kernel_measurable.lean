-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02a_original_rightcont_predictable_kernel_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:01:46.060374+00:00
-- url     : https://prove2.me/submissions/4ad96299-bca7-469f-aa57-0fcc8b8bc6ca

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_rational_grid_actual_jump_coverage
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_first_candidate_filter_covers_original_jumps
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_jump_kernel_of_measurable_enumeration
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_joint_original_predictable_mark_lift_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (K : Ω → @Measure ((ℝ≥0 × Ω) × ℝ)
      (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
        (inferInstance : MeasurableSpace ℝ)))
    (hK : ∀ ω, K ω =
      @Measure.map (ℝ≥0 × ℝ) ((ℝ≥0 × Ω) × ℝ)
        (inferInstance : MeasurableSpace (ℝ≥0 × ℝ))
        (@Prod.instMeasurableSpace _ _ 𝓕.rightCont.predictable
          (inferInstance : MeasurableSpace ℝ))
        (fun p : ℝ≥0 × ℝ => ((p.1, ω), p.2))
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) :
    AEMeasurable K P := by
  classical
  obtain ⟨Y, hpath, _, _, _⟩ := avram_wave5_04_source_rightCont_levy_lift X
  obtain ⟨D, hcount, hdense⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  have hnonempty : D.Nonempty := hdense.nonempty
  obtain ⟨grid, hgrid⟩ := hcount.exists_eq_range hnonempty
  have hdenseGrid : DenseRange grid := by
    change Dense (Set.range grid)
    rw [← hgrid]
    exact hdense
  obtain ⟨pairs, hpairs⟩ := exists_surjective_nat (ℕ × ℚ)
  let T : ℕ → Ω → ℝ≥0 := fun k ω =>
    (⨅ n : ℕ, {ω : Ω | grid (pairs k).1 < grid n ∧
        Y.X (grid n) ω < ((pairs k).2 : ℝ)}.piecewise
      (fun _ => (grid n : ℝ≥0∞)) (fun _ => ⊤) ω).toNNReal
  have hTC := avram_wave5_02a_rational_grid_actual_jump_coverage
    Y grid hdenseGrid pairs hpairs
  have hT : ∀ n, Measurable (T n) := hTC.1
  have hCover := hTC.2
  let A : ℕ → Set Ω := fun n => {ω |
    0 < T n ω ∧
    Y.X (T n ω) ω -
      Function.leftLim (fun u : ℝ≥0 => Y.X u ω) (T n ω) ≠ 0 ∧
    ∀ m < n, T m ω ≠ T n ω}
  have hFilter := avram_wave5_02a_actual_jump_candidates_measurable_dedup Y T hT
  have hA : ∀ n, MeasurableSet (A n) := hFilter.1
  have hActive : ∀ ω n, ω ∈ A n → 0 < T n ω ∧
      Y.X (T n ω) ω -
        Function.leftLim (fun v : ℝ≥0 => Y.X v ω) (T n ω) ≠ 0 := by
    intro ω n hn
    exact ⟨hn.1, hn.2.1⟩
  have hInject : ∀ ω n m, ω ∈ A n → ω ∈ A m → T n ω = T m ω → n = m := by
    intro ω n m hn hm heq
    by_contra hne
    exact hFilter.2 ω n m hn hm hne heq
  have hCoverActive := (avram_wave5_02a_first_candidate_filter_covers_original_jumps
    Y T hT hCover).2
  let f : ℕ → Ω → ℝ≥0 × ℝ := fun n ω =>
    (T n ω, Y.X (T n ω) ω -
      Function.leftLim (fun v : ℝ≥0 => Y.X v ω) (T n ω))
  have hf : ∀ n, Measurable (f n) := by
    intro n
    exact (hT n).prodMk
      ((avram_wave4_04a_actual_levy_jumpmark_joint_measurable Y).comp
        ((hT n).prodMk measurable_id))
  have hEnum := avram_wave5_02a_actual_jump_measure_eq_distinct_enumerated_diracs
    Y T A hActive hInject hCoverActive
  obtain ⟨κ, hfinite, hκ⟩ :=
    avram_wave5_02a_original_jump_kernel_of_measurable_enumeration Y A hA f hf hEnum
  letI : IsSFiniteKernel κ := hfinite
  apply avram_wave5_02a_original_predictable_kernel_measurable_of_source_sfinite_kernel
    Y κ hκ K
  · intro ω
    rw [hK ω, hκ ω, hpath]
  · exact avram_wave5_02a_joint_original_predictable_mark_lift_measurable 𝓕.rightCont
