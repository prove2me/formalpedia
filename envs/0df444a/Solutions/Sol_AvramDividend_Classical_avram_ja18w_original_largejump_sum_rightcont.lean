-- Prove2me | solution 1 for AvramDividend.Classical.avram_ja18w_original_largejump_sum_rightcont
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T11:08:53.714462+00:00
-- url     : https://prove2.me/submissions/af2b631d-d610-440c-a98c-30f35a471d33

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
import Theorems.Thm_AvramDividend_Classical_avram_ja18f_finite_marked_step_sum_right_continuous
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

/-- Literal original finite jump sums are right-continuous on each path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) :
    ∀ (ω : Ω) (t : ℝ≥0),
      ContinuousWithinAt
        (fun u : ℝ≥0 =>
          avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω)
        (Set.Ici t) t := by
  intro ω t
  let T : ℝ≥0 := t + 1
  let j : ℝ≥0 → ℝ :=
    fun u => X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
  let L : ℝ≥0 → ℝ := fun u =>
    avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω
  obtain ⟨F, hF, hLF⟩ :=
    avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
      X ω T
  let g : ℝ≥0 → ℝ :=
    fun s => ∑ u ∈ F, if u ≤ s then j u else 0
  have hLocal (s : ℝ≥0) (hs : s ≤ T) : L s = g s := by
    obtain ⟨Fs, hFs, hLs⟩ :=
      avram_p4_h_gaussian_original_largejump_integral_eq_actual_finite_sum
        X ω s
    have hId : Fs = F.filter (fun u => u ≤ s) := by
      ext u
      rw [hFs u, Finset.mem_filter, hF u]
      constructor
      · rintro ⟨hpos, hus, hmark⟩
        exact ⟨⟨hpos, hus.trans hs, hmark⟩, hus⟩
      · rintro ⟨⟨hpos, _, hmark⟩, hus⟩
        exact ⟨hpos, hus, hmark⟩
    dsimp [L, g]
    rw [hLs, hId]
    simp only [Finset.sum_filter]
    rfl
  have hStep : ContinuousWithinAt g (Set.Ici t) t := by
    exact avram_ja18f_finite_marked_step_sum_right_continuous
      F (fun u : ℝ≥0 => u) j t
  have htT : t < T := by
    dsimp [T]
    exact lt_add_of_pos_right t (by norm_num)
  have hEventually : L =ᶠ[𝓝[Set.Ici t] t] g := by
    filter_upwards
      [(eventually_lt_nhds htT).filter_mono nhdsWithin_le_nhds]
      with s hs
    exact hLocal s hs.le
  have hAt : L t = g t := hLocal t htT.le
  change Tendsto L (𝓝[Set.Ici t] t) (𝓝 (L t))
  rw [hAt]
  exact hStep.congr' hEventually.symm
